-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyZeroRetainedError.radial_original_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:13:42.907824+00:00
-- url     : https://prove2.me/submissions/e0f00d44-68a8-4777-b371-2d5162de6c4e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024
import Theorems.Thm_OAI_SevenEighths_CenteredMomentNaturalReflection_original_inverse_reflection
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace

theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

end EisensteinSchwartzPoisson

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]

theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (eisEmbedding (b + c * z))‖) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (eisEmbedding b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (eisEmbedding (b + c * latticeCoordEquiv.symm p))‖) := by
    convert (preTransparency := .instances) hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change eisEmbedding b + eisEmbedding c *
        eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (latticeCoordEquiv.symm.summable_iff).mp hpair

theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (eisEmbedding z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma nonzeroIdeal_norm_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun I : NonzeroIdeal=>(Ideal.absNorm I.1:ℝ)^(-σ)) := by
  have h := (fullIdealWeight_summable_norm (σ:ℂ) (by simpa using hσ)).subtype (fun I=>I≠0)
  apply h.congr
  intro I
  change ‖fullIdealWeight (σ:ℂ) I.1‖=(Ideal.absNorm I.1:ℝ)^(-σ)
  rw [fullIdealWeight,if_neg I.2]
  simpa only [Complex.neg_re,Complex.ofReal_re,Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (nonzeroIdeal_norm_pos I) (-(σ:ℂ)))

end

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

end CompletedGauss

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

theorem annulus_bounds (x : ℝ) : 0 ≤ annulus x ∧ annulus x ≤ 1 := by
  by_cases hx : x ≤ 1/4
  · rw [annulus_zero_low x hx]; constructor <;> norm_num
  have hm := cutoff_antitone (show x ≤ 2*x by linarith)
  have h₁ := cutoff_bounds x
  have h₂ := cutoff_bounds (2*x)
  unfold annulus
  constructor <;> linarith

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

theorem dyadicWeight_bounds (n : ℤ) (q : ℝ) :
    0 ≤ dyadicWeight n q ∧ dyadicWeight n q ≤ 1 := annulus_bounds _

theorem dyadicWeight_outside_pair (q : ℝ) (k : ℤ)
    (hlo : dyadicScale k ≤ q) (hhi : q < dyadicScale (k+1))
    (n : ℤ) (hn : n ∉ ({k+1,k+2} : Finset ℤ)) : dyadicWeight n q=0 := by
  have hn₁ : n ≠ k+1 := by simpa using fun h => hn (by simp [h])
  have hn₂ : n ≠ k+2 := by simpa using fun h => hn (by simp [h])
  by_cases hnk : n ≤ k
  · exact dyadicWeight_zero_high n q ((zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnk).trans hlo)
  · have hkn : k+3 ≤ n := by omega
    have hmono : dyadicScale (k+3) ≤ dyadicScale n :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
    have he : dyadicScale (k+3)=4*dyadicScale (k+1) := by
      rw [show k+3=(k+1)+1+1 by omega,dyadicScale_add,dyadicScale_add]
      ring
    apply dyadicWeight_zero_low
    rw [he] at hmono
    linarith

theorem dyadicWeight_finite (q : ℝ) : (Function.support (fun n => dyadicWeight n q)).Finite := by
  by_cases hq : 0 < q
  · obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
    apply (Set.toFinite (({k+1,k+2} : Finset ℤ) : Set ℤ)).subset
    intro n hn
    by_contra hh
    exact hn (dyadicWeight_outside_pair q k hlo hhi n hh)
  · have hz : ∀ n,dyadicWeight n q=0 := fun n =>
      dyadicWeight_zero_low n q ((le_of_not_gt hq).trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))
    simp [hz]

theorem dyadicWeight_summable (q : ℝ) : Summable (fun n => dyadicWeight n q) :=
  summable_of_hasFiniteSupport (dyadicWeight_finite q)

theorem dyadicWeight_partition (q : ℝ) (hq : 0 < q) : ∑' n,dyadicWeight n q=1 := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
  rw [tsum_eq_sum (s := {k+1,k+2}) (dyadicWeight_outside_pair q k hlo hhi)]
  change dyadicScale k ≤ q at hlo
  change q < dyadicScale (k+1) at hhi
  have hk : k+1 ≠ k+2 := by omega
  rw [Finset.sum_pair hk]
  simp only [dyadicWeight,annulus]
  have h₁ : 2*(q/dyadicScale (k+1))=q/dyadicScale k := by
    rw [dyadicScale_add]; field_simp
  have h₂ : 2*(q/dyadicScale (k+2))=q/dyadicScale (k+1) := by
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]; field_simp
  rw [h₁,h₂,cutoff_zero _ ((le_div_iff₀ (dyadicScale_pos k)).mpr (by simpa using hlo))]
  have hs : q/dyadicScale (k+2) ≤ 1/2 := by
    apply (div_le_iff₀ (dyadicScale_pos (k+2))).mpr
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]
    linarith
  rw [cutoff_one _ hs]
  ring

theorem retained_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then dyadicWeight n q else 0) :=
  (dyadicWeight_summable q).indicator {n | Retained R n}

theorem discarded_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then 0 else dyadicWeight n q) := by
  have h := (dyadicWeight_summable q).sub (retained_summable R q)
  convert (preTransparency := .instances) h using 1
  ext n
  split_ifs <;> simp

theorem retained_add_discarded (R q : ℝ) (hq : 0 < q) :
    retainedWeight R q+discardedWeight R q=1 := by
  rw [retainedWeight,discardedWeight,← (retained_summable R q).tsum_add (discarded_summable R q)]
  convert (preTransparency := .instances) dyadicWeight_partition q hq using 1
  apply tsum_congr
  intro n
  split_ifs <;> simp

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem retainedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : retainedWeight R q=0 := by
  simp [retainedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem discardedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : discardedWeight R q=0 := by
  simp [discardedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem retainedWeight_nonneg (R q : ℝ) : 0 ≤ retainedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact (dyadicWeight_bounds n q).1
  · exact le_rfl

theorem discardedWeight_nonneg (R q : ℝ) : 0 ≤ discardedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact le_rfl
  · exact (dyadicWeight_bounds n q).1

theorem retainedWeight_bounds (R q : ℝ) : 0 ≤ retainedWeight R q ∧ retainedWeight R q ≤ 1 := by
  refine ⟨retainedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := discardedWeight_nonneg R q
    linarith
  · rw [retainedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem discardedWeight_bounds (R q : ℝ) : 0 ≤ discardedWeight R q ∧ discardedWeight R q ≤ 1 := by
  refine ⟨discardedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := retainedWeight_nonneg R q
    linarith
  · rw [discardedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem discardedWeight_zero_below (R q : ℝ) (hq : q ≤ R) : discardedWeight R q=0 := by
  by_cases hp : 0 < q
  · unfold discardedWeight
    trans ∑' _n : ℤ, (0:ℝ)
    · apply tsum_congr
      intro n
      split_ifs with hn
      · rfl
      · by_contra hne
        exact hn ⟨q,hp,hq,subset_tsupport _ hne⟩
    · exact tsum_zero
  · exact discardedWeight_zero_nonpos R q (le_of_not_gt hp)

theorem discardedWeight_support (R q : ℝ) (hq : discardedWeight R q ≠ 0) : R < q :=
  lt_of_not_ge (fun h => hq (discardedWeight_zero_below R q h))

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAbsoluteEnergy
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

theorem radial_norm_summable (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖Φ (‖eisEmbedding z‖^2/K)‖) := by
  simpa only [scaledRadialTest_apply] using
    actual_eisenstein_summable_norm (scaledRadialTest Φ K hK)

end SevenEighths.CenteredMomentAbsoluteEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PositiveSummability
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentPositiveSummability
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceMass
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile CenteredMomentDivisorRetained
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction CenteredMomentDivisorAllocation
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O

lemma bounded_radial_summable (F:O→ℂ) (B:ℝ) (hF:∀z,‖F z‖≤B)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (f:=fun z:O=>B^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    split_ifs
    · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hF z) 2)
        (Complex.abs_re_le_norm _) (abs_nonneg _) (sq_nonneg _)
    · simp only [norm_zero]
      positivity
  · exact (radial_norm_summable Φ K hK).mul_left _

end SevenEighths.CenteredMomentPositiveSummability

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

theorem coefficient_norm_le (χ : Character) (inverse : Bool) (I : Ideal O) :
    ‖coefficient χ inverse I‖ ≤ 1 := by
  cases inverse
  · exact idealCoeff_norm_le_one χ I
  · change ‖(UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      (idealCoeff_norm_le_one χ I)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Set Complex
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDyadic HeckeDetectorFourier

lemma norm_phase (x D : ℝ) (hx : 0<x) (hD : 0<D) (s : ℂ) (t : ℝ) :
    (x : ℂ)^(-s)*FourierBridge.logPhase t (Real.log (x/D)) =
      (D : ℂ)^(-s)*((x/D : ℝ) : ℂ)^(-HeckeDyadic.shift s.re (2*Real.pi*t-s.im)) := by
  have hxD : 0<x/D := div_pos hx hD
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxD.ne')]
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hD.le,
    ← Complex.ofReal_log hxD.le]
  unfold FourierBridge.logPhase HeckeDyadic.shift
  rw [← Complex.exp_add, ← Complex.exp_add, Real.log_div hx.ne' hD.ne']
  congr 1
  have hs : s=(s.re : ℂ)+(s.im : ℂ)*I := (Complex.re_add_im s).symm
  rw [hs]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
  push_cast
  ring

lemma polynomial_eq_finite (χ : Character) (inverse : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (S : Finset (Ideal O))
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ J∈S,
        coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
          (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq) := by
  unfold polynomial
  congr 1
  let f : Ideal O→ℂ := fun J => coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
    (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)
  have hf : Function.support f ⊆ {J : Ideal O | J≠0} := by
    intro J hJ hzero
    subst J
    apply hJ
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have he := tsum_subtype_eq_of_support_subset hf
  change (∑' J : {J : Ideal O // J≠0}, f J.val)=_
  apply he.trans
  apply tsum_eq_sum
  intro J hJ
  by_cases hj : J=0
  · subst J
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have hw : W ((J.absNorm : ℝ)/D)=0 := by
    by_contra hw
    exact hJ (hcover J hj hw)
  simp [f,hw]

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScale
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge

theorem scale_normalization (l : ℝ) :
    ((Real.exp l : ℝ) : ℂ)^(-(1/2 : ℂ))=Complex.exp (-(l : ℂ)/2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos l).ne'),
    ←Complex.ofReal_log (Real.exp_pos l).le,Real.log_exp]
  congr 1
  ring

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic
open ConcretePrimeRowBridge hiding O

theorem scaleSupport_cover (W : ℝ→ℂ) (a b upper l : ℝ) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hl : l≤upper) :
    ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈scaleSupport upper b := by
  intro J hJ hw
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hh := (div_le_iff₀ (Real.exp_pos l)).mp (hWs hw).2
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hl) hb
  have hn : (J.absNorm : ℝ)≤Real.exp upper*b := by nlinarith
  exact_mod_cast hn.trans (Nat.le_ceil _)

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ComparisonReflection
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily HeckePrimitive ActualEisensteinCubic ConcreteTraceCRT
open EisensteinSchwartzPoisson ConcretePrimeRowBridge GaussGeneratorTransport
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma inverse_half_power (X : ℝ) (hX : 0≤X) :
    (X:ℂ)^(-(1/2:ℂ))=(Real.sqrt X:ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (Complex.ofReal_cpow hX (1/2)).symm

lemma polynomial_plain (η : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial η false W X 0 0=
      (Real.sqrt X:ℂ)⁻¹*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
    Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,
    sub_zero,neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.norm]
  rw [inverse_half_power X hX.le]

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionDeletion
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectionDeletion
open HeckeFamily CenteredMomentComparisonReflection UniqueFactorizationMonoid
open IdealMobiusDivisorSum EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma reflected_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo (paperRadialFourier W) := by
  obtain ⟨s,C,hC,hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, by positivity, ?_⟩
  intro x hx
  exact (mul_le_mul_of_nonneg_right (by nlinarith : x^2 ≤ (1+x)^2)
    (norm_nonneg _)).trans (hb W x hx.le)

lemma inverse_norm_sq_summable : Summable (fun I : NI => (norm I ^ 2)⁻¹) := by
  have h := CompletedGauss.nonzeroIdeal_norm_rpow_summable 2 (by norm_num)
  convert (preTransparency := .instances) h using 1
  funext I
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rfl

lemma radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun I : NI => ‖F (norm I / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  apply (inverse_norm_sq_summable.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  have hx := div_pos (norm_pos I) hX
  have h : ‖F (norm I / X)‖ ≤ C / (norm I / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma plain_summable (η : Character) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun I : NI => idealCoeff η I.val * F (norm I / X)) := by
  apply Summable.of_norm
  apply (radial_summable_norm F hF X hX).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I.val)

lemma subset_product_nonzero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    (∏ P ∈ S, P) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)
lemma subset_product_norm_pos (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    0 < (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS))

lemma subset_product_moebius (D : Finset (Ideal O)) (hD : ∀ P ∈ D, Prime P) :
    (moebius (∏ P ∈ D,P) : ℂ) = (-1 : ℂ)^D.card := by
  have hf : normalizedFactors (∏ P ∈ D,P) = D.val := by
    simpa using normalizedFactors_prod_of_prime (m := D.val) hD
  have hs : Squarefree (∏ P ∈ D,P) := by
    rw [squarefree_iff_nodup_normalizedFactors (subset_product_nonzero D hD), hf]
    exact D.nodup
  rw [hs.moebius_eq, factors_eq_normalizedFactors, hf]
  simp

end SevenEighths.CenteredMomentReflectionDeletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionMass
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionMass
open CenteredMomentReflectionDeletion HeckeFamily UniqueFactorizationMonoid
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

lemma weight_nonneg (I : Ideal O) : 0 ≤ weight I := by unfold weight; positivity
lemma weight_mul (I J : Ideal O) : weight (I*J) = weight I * weight J := by
  simp only [weight, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv_rev]
  ring
lemma weight_one : weight (1 : Ideal O) = 1 := by simp [weight]
lemma weight_pow (I : Ideal O) (n : ℕ) : weight (I ^n) = weight I ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using weight_one
  | succ n ih => rw [pow_succ,weight_mul,ih,pow_succ]
lemma weight_prod (S : Finset (Ideal O)) (f : Ideal O → Ideal O) :
    weight (∏ P ∈ S,f P) = ∏ P ∈ S,weight (f P) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using weight_one
  | @insert P S h ih => simp only [Finset.prod_insert h,weight_mul,ih]
lemma prime_weight_lt_one (P : Ideal O) (hP : Prime P) : weight P < 1 := by
  have h : (1:ℝ) < P.absNorm := by
    have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
    exact_mod_cast (by omega : 1 < P.absNorm)
  have hs : 1 < Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using h
  exact inv_lt_one_of_one_lt₀ hs

lemma reconstruct_exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) :
    (∏ P : S,P.val ^ exponents S I P) = I.val.val := by
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P)]
  exact (Finset.prod_multiset_count_of_subset (normalizedFactors I.val.val) S I.property).symm.trans
    (Ideal.prod_normalizedFactors_eq_self I.val.property)
lemma exponents_injective (S : Finset (Ideal O)) : Function.Injective (exponents S) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  rw [← reconstruct_exponents S I,← reconstruct_exponents S J,h]
lemma weight_exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) :
    weight I.val.val = ∏ P : S,weight P.val ^ exponents S I P := by
  conv_lhs => rw [← reconstruct_exponents S I]
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P),
    Finset.prod_coe_sort S (fun P => weight P ^ (normalizedFactors I.val.val).count P), weight_prod]
  simp only [weight_pow]

lemma hasSum_geometric_pi {α : Type*} [Fintype α] (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a < 1) :
    HasSum (fun n : α → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹) := by
  classical
  apply Fintype.induction_empty_option (P := fun β _ => ∀ (r : β → ℝ),
    (∀ a, 0 ≤ r a) → (∀ a, r a < 1) →
    HasSum (fun n : β → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹)) ?_ ?_ ?_ α r hr hr1
  · intro α β _ e ih r hr hr1
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (r ∘ e) (fun a => hr (e a)) (fun a => hr1 (e a))
    let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have he := E.hasSum_iff.mpr h
    convert (preTransparency := .instances) he using 1
    · funext n
      exact (e.prod_comp (fun b => r b ^ n b)).symm
    · exact (e.prod_comp (fun b => (1-r b)⁻¹)).symm
  · intro r _ _
    simp
  · intro α _ ih r hr hr1
    have h0 := hasSum_geometric_of_lt_one (hr none) (hr1 none)
    have ht := ih (fun a => r (some a)) (fun a => hr (some a)) (fun a => hr1 (some a))
    have hs := h0.summable.mul_of_nonneg ht.summable (fun n => pow_nonneg (hr none) n)
      (fun n => Finset.prod_nonneg (fun a _ => pow_nonneg (hr (some a)) (n a)))
    have hp := h0.mul ht hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hp
    simpa only [Function.comp_def, Fintype.prod_option, Equiv.piOptionEquivProd_apply] using he

lemma smooth_summable (S : Finset (Ideal O)) (hS : ∀ P ∈ S,Prime P) :
    Summable (fun I : SmoothIdeal S => weight I.val.val) := by
  have hs := (hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))).summable
  exact (hs.comp_injective (exponents_injective S)).congr (fun I => (weight_exponents S I).symm)

lemma smooth_mass_le_euler (S : Finset (Ideal O)) (hS : ∀ P ∈ S,Prime P) :
    (∑' I : SmoothIdeal S,weight I.val.val) ≤ ∏ P ∈ S,(1-weight P)⁻¹ := by
  have hh := hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))
  have h := Summable.tsum_le_tsum_of_inj (exponents S) (exponents_injective S)
    (fun n _ => Finset.prod_nonneg (fun P _ => pow_nonneg (weight_nonneg P.val) (n P)))
    (fun I => (weight_exponents S I).le) (smooth_summable S hS) hh.summable
  rw [hh.tsum_eq,Finset.prod_coe_sort S (fun P => (1-weight P)⁻¹)] at h
  exact h

lemma deletion_mass (S : Finset (Ideal O)) :
    (∑ D ∈ S.powerset, weight (∏ P ∈ D,P)) = ∏ P ∈ S,(1+weight P) := by
  simp_rw [weight_prod]
  exact (Finset.prod_one_add S).symm

lemma localMass_nonneg (P : Ideal O) (hP : Prime P) : 0 ≤ localMass P := by
  exact div_nonneg (by linarith [weight_nonneg P]) (sub_pos.mpr (prime_weight_lt_one P hP)).le
lemma prime_weight_le (P : Ideal O) (hP : Prime P) : weight P ≤ 3/4 := by
  have hn : (2:ℝ) ≤ P.absNorm := by
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩ : 2 ≤ P.absNorm)
  have hs : 4/3 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
  nlinarith
lemma localMass_le_seven (P : Ideal O) (hP : Prime P) : localMass P ≤ 7 := by
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith [prime_weight_le P hP]
lemma localMass_le_three (P : Ideal O) (hP : Prime P) (hn : (4:ℝ) ≤ P.absNorm) :
    localMass P ≤ 3 := by
  have hs : 2 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hw : weight P ≤ 1/2 := by
    rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
    linarith
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith

theorem euler_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P),
      (∏ P ∈ S,localMass P) ≤ C * (Ideal.absNorm (∏ P ∈ S,P) : ℝ)^ε := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop (3:ℝ)))
  let K : ℕ := ⌈max 4 B⌉₊
  let smallIdeals := ConcretePrimeRowBridge.idealsUpTo K
  have hK : max 4 B ≤ (K:ℝ) := Nat.le_ceil _
  refine ⟨(7:ℝ)^smallIdeals.card,by positivity,?_⟩
  intro S hS
  have hpoint (P : Ideal O) (hP : P ∈ S) :
      localMass P ≤ (if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε := by
    have hn : (1:ℝ) ≤ P.absNorm := by
      have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hS P hP⟩
      exact_mod_cast (by omega : 1 ≤ P.absNorm)
    have he : 1 ≤ (P.absNorm:ℝ)^ε := Real.one_le_rpow hn hε.le
    by_cases hp : P ∈ smallIdeals
    · simp only [if_pos hp]
      exact (localMass_le_seven P (hS P hP)).trans (by nlinarith)
    · have hpk : (K:ℝ) < P.absNorm := by
        have hh : ¬ P.absNorm ≤ K := by
          intro h
          apply hp
          exact ConcretePrimeRowBridge.mem_idealsUpTo.mpr ⟨by exact_mod_cast hn,h⟩
        exact_mod_cast Nat.lt_of_not_ge hh
      have h4 : (4:ℝ) ≤ P.absNorm := (le_max_left _ _).trans (hK.trans hpk.le)
      have hb : B ≤ (P.absNorm:ℝ) := (le_max_right _ _).trans (hK.trans hpk.le)
      simp only [if_neg hp,one_mul]
      exact (localMass_le_three P (hS P hP) h4).trans (hB _ hb)
  have hc : (S.filter (· ∈ smallIdeals)).card ≤ smallIdeals.card :=
    Finset.card_le_card (fun P hP => (Finset.mem_filter.mp hP).2)
  calc
    (∏ P ∈ S,localMass P) ≤ ∏ P ∈ S,((if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε) :=
      Finset.prod_le_prod (fun P hP => localMass_nonneg P (hS P hP)) hpoint
    _ = (7:ℝ)^(S.filter (· ∈ smallIdeals)).card * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
      rw [Finset.prod_mul_distrib,← Finset.prod_filter]
      simp only [Finset.prod_const,Real.finsetProd_rpow S _ (fun _ _ => Nat.cast_nonneg _) ε,
        map_prod,Nat.cast_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc) (Real.rpow_nonneg (by positivity) _)

lemma coefficient_norm_le (η ηi : Character) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (hD : ∀ P ∈ D,Prime P) (H : SmoothIdeal S) :
    ‖coefficient η ηi S D H‖ ≤ weight (∏ P ∈ D,P) * weight H.val.val := by
  rw [coefficient,subset_product_moebius D hD]
  simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h : ‖idealCoeff η (∏ P ∈ D,P)‖ * ‖idealCoeff ηi H.val.val‖ ≤ 1 :=
    (mul_le_mul (idealCoeff_norm_le_one η _) (idealCoeff_norm_le_one ηi _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  apply (div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)).trans_eq
  simp only [CenteredMomentReflectionDeletion.norm,weight,Real.sqrt_mul (Nat.cast_nonneg _),one_div,mul_inv_rev]
  ring

lemma coefficient_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (D : Finset (Ideal O)) (hD : D ⊆ S) :
    Summable (fun H : SmoothIdeal S => ‖coefficient η ηi S D H‖) := by
  apply ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  exact fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hD hP)) H

lemma coefficient_mass_le_euler (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
      ∏ P ∈ S,localMass P := by
  have hD (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      (∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        weight (∏ P ∈ D,P) * (∏ P ∈ S,(1-weight P)⁻¹) := by
    have hsub := Finset.mem_powerset.mp hD
    apply ((coefficient_summable_norm η ηi S hS D hsub).tsum_le_tsum
      (fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hsub hP)) H)
      ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P)))).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (smooth_mass_le_euler S hS) (weight_nonneg _)
  apply (Finset.sum_le_sum hD).trans_eq
  rw [← Finset.sum_mul,deletion_mass,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  exact (div_eq_mul_inv _ _).symm

lemma coefficient_mass_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) := by
  exact summable_sum (fun D hD => coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD))

theorem reflection_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P)
      (η ηi : Character),
      Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) ∧
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        C * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := euler_mass_subpower ε hε
  exact ⟨C,hC,fun S hS η ηi => ⟨coefficient_mass_summable η ηi S hS,
    (coefficient_mass_le_euler η ηi S hS).trans (hbound S hS)⟩⟩

end SevenEighths.CenteredMomentReflectionMass
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum
namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentFrequencyScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge FourierBridge
open CenteredMomentScaleSupremum (scaleTest scaleTest_support)
open HeckeInverseAmplification (scaleProfile scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)

lemma ratio_frequency_phase (x l freq : ℝ) (hx : 0<x) :
    (((x/Real.exp l : ℝ):ℂ)^(-_root_.OAI.SevenEighths.HeckeDyadic.shift 0 freq))=
      logPhase (freq/(2*Real.pi)) (-l)*logPhase (freq/(2*Real.pi)) (Real.log x) := by
  have ht : 2*Real.pi*(freq/(2*Real.pi))=freq := by field_simp
  have hh := norm_phase x (Real.exp l) hx (Real.exp_pos l) 0 (freq/(2*Real.pi))
  rw [ht] at hh
  simp only [neg_zero,Complex.cpow_zero,one_mul,zero_re,zero_im,sub_zero] at hh
  rw [←hh,Real.log_div hx.ne' (Real.exp_pos l).ne',Real.log_exp]
  rw [show Real.log x-l=(-l)+Real.log x by ring,logPhase_add]

theorem frequencyScaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    polynomial χ inv W (Real.exp l) 0 freq=
      logPhase (freq/(2*Real.pi)) (-l)*frequencyScaleSum χ inv W freq S l := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 freq S hc,scale_normalization]
  unfold frequencyScaleSum
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h0 : J=0
  · subst J
    simp only [coefficient_zero,zero_mul,mul_zero]
  have hpos : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h0)
  rw [ratio_frequency_phase _ l freq hpos,Real.exp_neg,div_eq_mul_inv]
  ring

end SevenEighths.CenteredMomentFrequencyScaleSupremum

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedAnnuli
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentReflectedAnnuli
open Set EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open CenteredMomentComparisonReflection LocalLogFourier

theorem normalized_annular_term (η : HeckeFamily.Character) (F : ℝ→ℂ)
    (s Y : ℝ) (hs : 0<s) (hY : 0<Y) :
    HeckeDyadic.polynomial η false (fun x=>(annulus (x/s):ℂ)*F x) Y 0 0=
      (Real.sqrt s:ℂ)*HeckeDyadic.polynomial η false (annularProfile F s) (s*Y) 0 0 := by
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ (mul_pos hs hY)]
  have he (x : ℝ) : (annulus ((x/Y)/s):ℂ)*F (x/Y)=
      annularProfile F s (x/(s*Y)) := by
    unfold annularProfile
    congr 2 <;> field_simp
  simp_rw [he]
  rw [Real.sqrt_mul hs.le,Complex.ofReal_mul]
  have hs' : (Real.sqrt s:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hs))
  field_simp

end SevenEighths.CenteredMomentReflectedAnnuli

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedSeries
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedSeries
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma dyadicIdealTerm_norm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) :
    ‖dyadicIdealTerm η F Y I n‖=
      dyadicWeight n ((I.val.absNorm:ℝ)/Y)*‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖ := by
  unfold dyadicIdealTerm
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (dyadicWeight_bounds _ _).1,norm_mul]
  ring

lemma dyadic_ideal_absolute (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun p : NI×ℤ=>‖dyadicIdealTerm η F Y p.1 p.2‖) := by
  apply (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr
  simp_rw [dyadicIdealTerm_norm]
  constructor
  · intro I
    exact (dyadicWeight_summable _).mul_right _
  · simp_rw [tsum_mul_right]
    have he (I : NI) : (∑'n : ℤ,dyadicWeight n ((I.val.absNorm:ℝ)/Y))=1 :=
      dyadicWeight_partition _ (div_pos (HeckeDyadic.norm_pos I) hY)
    simp_rw [he,one_mul]
    exact (plain_summable η F hF Y hY).norm

end SevenEighths.CenteredMomentReflectedSeries

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedTruncation
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedTruncation
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open CenteredMomentReflectedSeries EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

theorem normalized_subseries (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) (A : Set ℤ) :
    Summable (fun n : ℤ=>if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0) ∧
    HeckeDyadic.polynomial η false
      (fun x=>(∑'n : ℤ,if n∈A then dyadicWeight n x else 0:ℝ)*F x) Y 0 0=
      ∑'n : ℤ,if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0 := by
  have hs := (dyadic_ideal_absolute η F hF Y hY).of_norm
  have hi : Summable (fun p : NI×ℤ=>if p.2∈A then dyadicIdealTerm η F Y p.1 p.2 else 0) :=
    hs.indicator {p : NI×ℤ | p.2∈A}
  have he (n : ℤ) : (if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0)=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,if n∈A then dyadicIdealTerm η F Y I n else 0 := by
    split_ifs with hn
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      congr 1
      apply tsum_congr
      intro I
      simp only [dyadicIdealTerm,dyadicWeight]
      ring
    · simp
  simp_rw [he]
  refine ⟨hi.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η _ Y hY]
  congr 1
  rw [hi.tsum_comm]
  apply tsum_congr
  intro I
  have ht (n : ℤ) : (if n∈A then dyadicIdealTerm η F Y I n else 0)=
      ((if n∈A then dyadicWeight n ((I.val.absNorm:ℝ)/Y) else 0:ℝ):ℂ)*
        (idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    split_ifs <;> simp only [dyadicIdealTerm,Complex.ofReal_zero,zero_mul] ; ring
  simp_rw [ht]
  rw [tsum_mul_right,←Complex.ofReal_tsum]
  ring

lemma retainedAnnuli_mem (R Y : ℝ) (hY : 0<Y) (n : ℤ) :
    n∈retainedAnnuli R Y hY ↔ Retained R n ∧ ∃q : ℝ,Y⁻¹≤q ∧ dyadicWeight n q≠0 := by
  exact (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).mem_toFinset

lemma original_norm_lower (I : NI) (Y : ℝ) (hY : 0<Y) :
    Y⁻¹≤(I.val.absNorm:ℝ)/Y := by
  have hn : (1:ℝ)≤I.val.absNorm := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property))
  simpa only [one_div] using div_le_div_of_nonneg_right hn hY.le

theorem retained_finite_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) :
    HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=
      ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have hh := (normalized_subseries η F hF Y hY {n | Retained R n}).2
  change HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=_ at hh
  rw [hh,tsum_eq_sum (s:=retainedAnnuli R Y hY)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Set.mem_ofPred_eq,if_pos ((retainedAnnuli_mem R Y hY n).mp hn).1]
  · intro n hn
    split_ifs with hr
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      have hz (I : NI) : dyadicWeight n ((I.val.absNorm:ℝ)/Y)=0 := by
        by_contra hne
        exact hn ((retainedAnnuli_mem R Y hY n).mpr ⟨hr,_,original_norm_lower I Y hY,hne⟩)
      have he (I : NI) : idealCoeff η I.val*
          ((annulus (((I.val.absNorm:ℝ)/Y)/dyadicScale n):ℂ)*F ((I.val.absNorm:ℝ)/Y))=0 := by
        change idealCoeff η I.val*((dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F _)=0
        rw [hz,Complex.ofReal_zero,zero_mul,mul_zero]
      simp_rw [he,tsum_zero,mul_zero]
    · rfl

end SevenEighths.CenteredMomentReflectedTruncation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionTails
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma ideal_norm_rpow_summable (B : ℕ) (hB : 2≤B) :
    Summable (fun I : NI=>(I.val.absNorm:ℝ)^(-(B:ℝ))) := by
  have hb : (1:ℝ)<B := by exact_mod_cast (by omega : 1<B)
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (B:ℂ)
    (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NI=>I.val))
  apply hs.congr
  intro I
  rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,if_neg I.property]
  change ‖((I.val.absNorm:ℝ):ℂ)^(-(B:ℂ))‖=_
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hi]
  simp

lemma plain_term_rapid_bound (η : Character) (F : ℝ→ℂ) (B : ℕ) (D Y : ℝ)
    (hY : 0<Y) (hF : ∀x : ℝ,0<x → x^B*‖F x‖≤D) (I : NI) :
    ‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤
      (D*Y^B)*(I.val.absNorm:ℝ)^(-(B:ℝ)) := by
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  have hx : 0<(I.val.absNorm:ℝ)/Y := div_pos hi hY
  have hb : ‖F ((I.val.absNorm:ℝ)/Y)‖≤D/((I.val.absNorm:ℝ)/Y)^B :=
    (le_div_iff₀ (pow_pos hx B)).mpr (by simpa only [mul_comm] using hF _ hx)
  calc
    _≤‖F ((I.val.absNorm:ℝ)/Y)‖:=by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)
    _≤D/((I.val.absNorm:ℝ)/Y)^B:=hb
    _=_:=by
      rw [Real.rpow_neg hi.le,Real.rpow_natCast,div_pow]
      field_simp

theorem plain_rapid_summable (η : Character) (F : ℝ→ℂ) (B : ℕ) (hB : 2≤B)
    (D Y : ℝ) (hY : 0<Y) (hF : ∀x : ℝ,0<x → x^B*‖F x‖≤D) :
    Summable (fun I : NI=>idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (plain_term_rapid_bound η F B D Y hY hF)
    ((ideal_norm_rpow_summable B hB).mul_left (D*Y^B))

theorem plain_rapid_bound (B : ℕ) (hB : 2≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character)(F : ℝ→ℂ)(D Y : ℝ),0≤D → 0<Y →
      (∀x : ℝ,0<x → x^B*‖F x‖≤D) →
      ‖HeckeDyadic.polynomial η false F Y 0 0‖≤C*D*(Y^B/Real.sqrt Y) := by
  let C := 1+∑' I : NI,(I.val.absNorm:ℝ)^(-(B:ℝ))
  have hs := ideal_norm_rpow_summable B hB
  have hnon : 0≤∑' I : NI,(I.val.absNorm:ℝ)^(-(B:ℝ)) :=
    tsum_nonneg (fun I=>Real.rpow_nonneg (HeckeDyadic.norm_pos I).le _)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro η F D Y hD hY hF
  have ht := plain_rapid_summable η F B hB D Y hY hF
  have hh := ht.norm.tsum_le_tsum (plain_term_rapid_bound η F B D Y hY hF)
    (hs.mul_left (D*Y^B))
  rw [tsum_mul_left] at hh
  have hb : ‖∑' I : NI,idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤D*Y^B*C := by
    exact (norm_tsum_le_tsum_norm ht.norm).trans (hh.trans
      (mul_le_mul_of_nonneg_left (by dsimp [C];linarith) (by positivity)))
  rw [polynomial_plain η F Y hY,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
  calc
    _≤(Real.sqrt Y)⁻¹*(D*Y^B*C):=mul_le_mul_of_nonneg_left hb (by positivity)
    _=C*D*(Y^B/Real.sqrt Y):=by ring

lemma discarded_rapid_control (F : ℝ→ℂ) (A B : ℕ) (D R : ℝ)
    (hD : 0≤D) (hR : 0<R) (hF : ∀x : ℝ,0<x → x^(B+A)*‖F x‖≤D) :
    ∀x : ℝ,0<x → x^B*‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤D/R^A := by
  intro x hx
  by_cases hz : CenteredMomentSectorLocalization.discardedWeight R x=0
  · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero,mul_zero]
    positivity
  have hRx := (CenteredMomentSectorLocalization.discardedWeight_support R x hz).le
  have hw := CenteredMomentSectorLocalization.discardedWeight_bounds R x
  have hnorm : ‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤‖F x‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hw.2
  apply (mul_le_mul_of_nonneg_left hnorm (pow_nonneg hx.le B)).trans
  apply (le_div_iff₀ (pow_pos hR A)).mpr
  calc
    _≤(x^B*‖F x‖)*x^A :=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRx A) (by positivity)
    _=x^(B+A)*‖F x‖ :=by rw [pow_add];ring
    _≤D :=hF x hx

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionLength
namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentComparisonReflection

lemma reflected_scale_bound (Z M n xi C Q R d h s : ℝ)
    (hZ : 1<Z) (_hC : 0≤C) (hQ : 0≤Q) (hd : 0≤d) (_hs : 0≤ s)
    (hcap : Q*R≤C*Z^M) (hdR : d≤R) (hh : 1≤h) (hsmax : s≤Z^(xi/2)) :
    s*(Q*d/(Z^n*h))≤C*Z^(M-n+xi/2) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hn : 0<Z^n := Real.rpow_pos_of_pos hz _
  have hp : Q*d≤C*Z^M := (mul_le_mul_of_nonneg_left hdR hQ).trans hcap
  have hy : Q*d/(Z^n*h)≤C*Z^M/Z^n := by
    calc
      _≤Q*d/Z^n := div_le_div_of_nonneg_left (mul_nonneg hQ hd) hn (by nlinarith)
      _≤C*Z^M/Z^n := div_le_div_of_nonneg_right hp hn.le
  calc
    _≤Z^(xi/2)*(C*Z^M/Z^n) := mul_le_mul hsmax hy (by positivity) (by positivity)
    _=C*Z^(M-n+xi/2) := by
      rw [Real.rpow_add hz,Real.rpow_sub hz]
      ring

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength
namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentReflectionRetainedLength
open CenteredMomentComparisonReflection CenteredMomentReflectedTruncation
open CenteredMomentSectorLocalization

lemma retained_scale_lower (R Y : ℝ) (hY : 0<Y) (n : ℤ)
    (hn : n∈retainedAnnuli R Y hY) : 1≤dyadicScale n*Y := by
  obtain ⟨hr,q,hq,hne⟩ := (retainedAnnuli_mem R Y hY n).mp hn
  have hs := (dyadicWeight_support n hne).2.le
  have hh := mul_le_mul_of_nonneg_right (hq.trans hs) hY.le
  simpa only [inv_mul_cancel₀ hY.ne'] using hh

theorem eventually_actual_retained_length (C box xi : ℝ) (hC : 0<C)
    (hbox : 1≤box) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(M a Q R d h : ℝ),
      0<Q → 0<d → Q*R≤C*Z^M → d≤R → 1≤h →
      ∀n : ℤ,∀hY : 0<Q*d/(Z^a*h),
      n∈retainedAnnuli (Z^(xi/4)) (Q*d/(Z^a*h)) hY →
      1≤dyadicScale n*(Q*d/(Z^a*h)) ∧
      0≤Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h)))) ∧
      Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h))))≤M-a+xi := by
  have hc := (tendsto_rpow_atTop (show 0<xi/2 by linarith)).eventually
    (eventually_ge_atTop (box*C))
  have hfour := (tendsto_rpow_atTop (show 0<xi/4 by linarith)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc,hfour] with Z hZ hconst h4
  refine ⟨hZ,?_⟩
  intro M a Q R d h hQ hd hcap hdR hh n hY hn
  have hz : 0<Z := zero_lt_one.trans hZ
  have hs : dyadicScale n≤Z^(xi/2) := by
    calc
      _≤4*Z^(xi/4) := retained_scale_le _ n ((retainedAnnuli_mem _ _ hY n).mp hn).1
      _≤Z^(xi/4)*Z^(xi/4) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _=Z^(xi/2) := by rw [←Real.rpow_add hz];congr 1;ring
  have hlo := retained_scale_lower _ _ hY n hn
  have hraw := reflected_scale_bound Z M a xi C Q R d h (dyadicScale n)
    hZ hC.le hQ.le hd.le (dyadicScale_pos n).le hcap hdR hh hs
  have hb : 1≤box*(dyadicScale n*(Q*d/(Z^a*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤_ :=mul_le_mul hbox hlo zero_le_one (by linarith)
  refine ⟨hlo,Real.logb_nonneg hZ hb,?_⟩
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hb)).mpr
  calc
    _≤box*(C*Z^(M-a+xi/2)) := mul_le_mul_of_nonneg_left hraw (by linarith)
    _=(box*C)*Z^(M-a+xi/2) :=by ring
    _≤Z^(xi/2)*Z^(M-a+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
    _=Z^(M-a+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

end SevenEighths.CenteredMomentReflectionRetainedLength

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionNegligible
namespace OAI

noncomputable section
open scoped ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily EisensteinSchwartzPoisson

lemma normalized_power_eq (Y : ℝ) (hY : 0<Y) (B : ℕ) :
    Y^B/Real.sqrt Y=Y^((B:ℝ)-1/2) := by
  rw [Real.rpow_sub hY,Real.rpow_natCast,Real.sqrt_eq_rpow]

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionTailMass
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectionTailMass
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma subset_norm_le (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S) :
    (Ideal.absNorm (∏P∈D,P):ℝ)≤(Ideal.absNorm (∏P∈S,P):ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS)))
    (map_dvd Ideal.absNorm (Finset.prod_dvd_prod_of_subset D S (fun P=>P) hD))

lemma restoration_norm_one (S : Finset (Ideal O)) (H : SmoothIdeal S) : 1≤norm H.val := by
  unfold CenteredMomentReflectionDeletion.norm
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr H.val.property))

lemma dual_scale_bounds (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S)
    (H : SmoothIdeal S) (Q X U : ℝ) (hQ : 0<Q) (hX : 0<X)
    (hcap : Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤U*X) :
    0<Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val) ∧
    Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)≤U := by
  have hd := subset_product_norm_pos D (fun P hP=>hS P (hD hP))
  have hh := norm_pos H.val
  refine ⟨by positivity,?_⟩
  calc
    _≤Q*(Ideal.absNorm (∏P∈D,P):ℝ)/X :=
      div_le_div_of_nonneg_left (by positivity) hX
        (by nlinarith [restoration_norm_one S H])
    _≤Q*(Ideal.absNorm (∏P∈S,P):ℝ)/X :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (subset_norm_le S D hS hD) hQ.le) hX.le
    _≤U := (div_le_iff₀ hX).mpr hcap

theorem coefficient_column_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
      (η ηi : Character)(f : Finset (Ideal O)→SmoothIdeal S→ℂ)(B : ℝ),0≤B →
      (∀D∈S.powerset,∀H,‖f D H‖≤B) →
      (∀D∈S.powerset,Summable (fun H=>coefficient η ηi S D H*f D H)) ∧
      ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*f D H‖≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*B := by
  obtain ⟨C,hC,hbound⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi f B hB hf
  have hs (D : Finset (Ideal O)) (hD : D∈S.powerset) :
      Summable (fun H : SmoothIdeal S=>‖coefficient η ηi S D H*f D H‖) := by
    apply ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B).of_nonneg_of_le
      (fun _=>norm_nonneg _)
    intro H
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
  refine ⟨fun D hD=>(hs D hD).of_norm,?_⟩
  calc
    _≤∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H*f D H‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun D hD=>norm_tsum_le_tsum_norm (hs D hD)))
    _≤∑D∈S.powerset,(∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)*B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [←tsum_mul_right]
      apply (hs D hD).tsum_le_tsum _
        ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B)
      intro H
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
    _≤_ := by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hbound S hS η ηi).2 hB

end SevenEighths.CenteredMomentReflectionTailMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedChoiceEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectedChoiceEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentReflectionDeletion CenteredMomentReflectionTailMass
open CenteredMomentNaturalPrimitive CenteredMomentReflectionRetainedLength
open Filter

local notation "O" => HeckeFamily.O

theorem eventually_natural_choice_geometry (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      let S := redundantSet χ.modulus ψ.modulus
      ∀u : Index S,
      let Y := (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈u.1.1.val,P):ℝ)/(Z^a*CenteredMomentReflectionDeletion.norm u.1.2.val)
      ∀hY : 0<Y,u.2∈retainedAnnuli (Z^(xi/4)) Y hY →
      1≤dyadicScale u.2*Y ∧
      0≤Real.log (dyadicScale u.2*Y) ∧
      Real.log (dyadicScale u.2*Y)≤(M-a+xi)*Real.log Z := by
  filter_upwards [eventually_actual_retained_length C 1 xi hC le_rfl hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod
  dsimp only
  intro u hY hu
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hD := subset_product_norm_pos u.1.1.val
    (fun P hP=>hS P ((Finset.mem_powerset.mp u.1.1.property) hP))
  have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤C*Z^M := by
    have hh : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by exact_mod_cast hcap
    exact hh.trans hmod
  have hh := hZ.2 M a _ _ _ _ hQ hD hc
    (subset_norm_le _ _ hS (Finset.mem_powerset.mp u.1.1.property))
    (restoration_norm_one _ u.1.2) u.2 hY hu
  simp only [one_mul] at hh
  refine ⟨hh.1,Real.log_nonneg hh.1,?_⟩
  have hz : 0<Real.log Z := Real.log_pos hZ.1
  have hlog := hh.2.2
  rw [Real.logb] at hlog
  exact (div_le_iff₀ hz).mp hlog

end SevenEighths.CenteredMomentReflectedChoiceEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RetainedReflection
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedReflection
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive CenteredMomentNaturalReflection
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma masked_decayTwo (F : ℝ→ℂ) (hF : DecayTwo F) (w : ℝ→ℝ)
    (hw : ∀x,0≤w x ∧ w x≤1) : DecayTwo (fun x=>(w x:ℂ)*F x) := by
  obtain ⟨D,hD,hb⟩ := hF
  refine ⟨D,hD,?_⟩
  intro x hx
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw x).1]
  apply (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) (hw x).2) (sq_nonneg x)).trans (hb x hx)

lemma column_retained_discarded (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) :
    HeckeDyadic.polynomial η false F Y 0 0=
      HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0+
      HeckeDyadic.polynomial η false (fun x=>(discardedWeight R x:ℂ)*F x) Y 0 0 := by
  have hr := plain_summable η _ (masked_decayTwo F hF _ (retainedWeight_bounds R)) Y hY
  have hd := plain_summable η _ (masked_decayTwo F hF _ (discardedWeight_bounds R)) Y hY
  simp only [CenteredMomentReflectionDeletion.norm] at hr hd
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ hY,polynomial_plain _ _ _ hY,
    ←mul_add,←hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro I
  have hp := retained_add_discarded R (norm I/Y) (div_pos (norm_pos I) hY)
  simp only [CenteredMomentReflectionDeletion.norm] at hp ⊢
  rw [←mul_add,←add_mul,←Complex.ofReal_add,hp,Complex.ofReal_one,one_mul]

lemma bounded_columns (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F) :
    ∃C : ℝ,0≤C ∧ ∀Y U : ℝ,0<Y → Y≤U →
      ‖HeckeDyadic.polynomial η false F Y 0 0‖≤C*U^(3/2:ℝ) := by
  obtain ⟨D,hD,hF⟩ := hF
  obtain ⟨C,hC,hb⟩ := plain_rapid_bound 2 (by omega)
  refine ⟨C*D,by positivity,?_⟩
  intro Y U hY hYU
  apply (hb η F D Y hD hY hF).trans
  rw [normalized_power_eq Y hY 2]
  norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY.le hYU (by norm_num)) (by positivity)

lemma reflected_column_summable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η ηi χ : Character) (F : ℝ→ℂ) (hF : DecayTwo F) (Q X : ℝ)
    (hQ : 0<Q) (hX : 0<X) (D : Finset (Ideal O)) (hD : D∈S.powerset) :
    Summable (fun H : SmoothIdeal S=>coefficient η ηi S D H*
      HeckeDyadic.polynomial χ false F
        (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0) := by
  obtain ⟨C,hC,hb⟩ := bounded_columns χ F hF
  obtain ⟨K,hK,hKb⟩ := coefficient_column_bound 1 (by norm_num)
  let U := Q*(Ideal.absNorm (∏P∈S,P):ℝ)/X
  have hu : 0<U := div_pos (mul_pos hQ (subset_product_norm_pos S hS)) hX
  exact (hKb S hS η ηi (fun E H=>HeckeDyadic.polynomial χ false F
    (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm H.val)) 0 0)
    (C*U^(3/2:ℝ)) (by positivity) (by
      intro E hE H
      have hscale := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) H Q X U hQ hX (by
        dsimp [U]
        rw [div_mul_cancel₀ _ hX.ne'])
      exact hb _ U hscale.1 hscale.2)).1 D hD

theorem original_retained_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : 𝓢(ℝ,ℂ))(X R : ℝ)(_hX : 0<X),
        let Q := (ψ.modulus.absNorm:ℝ)
        let Y := fun (D : Finset (Ideal O))(H : SmoothIdeal S)=>Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)
        HeckeDyadic.polynomial χ false W X 0 0=
          G*((∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
            HeckeDyadic.polynomial χ.inverse false
              (fun x=>(retainedWeight R x:ℂ)*paperRadialFourier W x) (Y D H) 0 0)+
            ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
            HeckeDyadic.polynomial χ.inverse false
              (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier W x) (Y D H) 0 0) := by
  obtain ⟨ψ,G,hp,hnp,hG,hcap,heq⟩ := original_inverse_reflection χ hn
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro W X R hX
  dsimp only
  rw [heq W X hX]
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hF := reflected_decayTwo W
  have hr := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (retainedWeight_bounds R)) _ X hQ hX D hD
  have hd := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (discardedWeight_bounds R)) _ X hQ hX D hD
  rw [←hr.tsum_add hd]
  apply tsum_congr
  intro H
  have hY := (dual_scale_bounds _ D hS (Finset.mem_powerset.mp hD) H
    (ψ.modulus.absNorm:ℝ) X ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈redundantSet χ.modulus ψ.modulus,P):ℝ)/X)
    hQ hX (by rw [div_mul_cancel₀ _ hX.ne'])).1
  change coefficient ψ ψ.inverse _ D H*HeckeDyadic.polynomial χ.inverse false
    (paperRadialFourier W) _ 0 0=_
  rw [column_retained_discarded χ.inverse _ hF R _ hY,mul_add]

end SevenEighths.CenteredMomentRetainedReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OriginalReflectionApproximation
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive
open CenteredMomentRetainedReflection
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma finiteAnnularColumn_eq (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) : finiteAnnularColumn η F R Y=
      HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0 := by
  rw [finiteAnnularColumn,dif_pos hY]
  exact (retained_finite_series η F hF R Y hY).symm

lemma radical_le_original (χ ψ : Character)
    (hcap : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm) :
    (Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by
  have hp : 1≤ψ.modulus.absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  exact_mod_cast (show (redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm by
    nlinarith)

end SevenEighths.CenteredMomentOriginalReflectionApproximation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OriginalReflectionEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionEnergy
open HeckeFamily CenteredMomentOriginalReflectionApproximation CenteredMomentNaturalPrimitive

lemma norm_sq_comparison (a b : ℂ) : ‖a‖^2≤2*‖b‖^2+2*‖a-b‖^2 := by
  have he : a=b+(a-b) := by ring
  have hh : ‖a‖≤‖b‖+‖a-b‖ := by nth_rw 1 [he];exact norm_add_le _ _
  nlinarith [norm_nonneg a,norm_nonneg b,norm_nonneg (a-b),sq_nonneg (‖b‖-‖a-b‖)]

end SevenEighths.CenteredMomentOriginalReflectionEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RadialPolynomialEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentRadialPolynomialEnergy
open HeckeFamily HeckeDyadic CenteredMomentFrequencyScaleSupremum
open CenteredMomentPositiveSummability ConcreteTraceCRT
open HeckeInverseAmplification
local notation "O" => HeckeFamily.O

lemma polynomial_bounded (W : ℝ→ℂ) (a b X : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,∀t : ℝ,‖polynomial χ false W X 0 t‖≤B := by
  let l:=Real.log X
  let S:=scaleSupport l b
  have hx : Real.exp l=X := Real.exp_log hX
  have hc : ∀I : Ideal O,I≠0 → W ((I.absNorm:ℝ)/Real.exp l)≠0 → I∈S :=
    scaleSupport_cover W a b l l hb hs le_rfl
  let B:=‖Complex.exp (-(l:ℂ)/2)‖*∑I∈S,‖W ((I.absNorm:ℝ)*Real.exp (-l))‖
  refine ⟨B,by dsimp [B];positivity,?_⟩
  intro χ t
  rw [←hx,frequencyScaleSum_eq_polynomial χ false W t S l hc,norm_mul,
    FourierBridge.logPhase_norm,one_mul]
  unfold frequencyScaleSum
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul,norm_mul,FourierBridge.logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (coefficient_norm_le χ false I)

lemma single_radial_summable (χ : O→Character) (P : O→ℂ) (t : O→ℝ)
    (W : ℝ→ℂ) (a b X Pbound : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support W⊆Set.Icc a b) (hP : ∀z,‖P z‖≤Pbound)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z:O=>if keep z then ‖polynomial (χ z) false W X 0 (t z)*P z‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB,hh⟩:=polynomial_bounded W a b X hb hX hs
  apply bounded_radial_summable _ (B*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul]
  exact mul_le_mul (hh _ _) (hP z) (norm_nonneg _) hB

end SevenEighths.CenteredMomentRadialPolynomialEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentOriginalRadialComparison
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentRadialPolynomialEnergy
local notation "O" => HeckeFamily.O

lemma finite_weighted (rows : Finset O) (keep : O→Prop) (F : O→ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) :
    (∑z : ↥(rows.filter keep),‖F z*(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)‖^2)=
    ∑z∈rows,if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0 := by
  simp_rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hΦ _)]
  rw [Finset.sum_coe_sort (rows.filter keep) (fun z:O=>‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re),Finset.sum_filter]

end SevenEighths.CenteredMomentOriginalRadialComparison

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.UniformReflectionApproximation
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentRetainedReflection CenteredMomentOriginalReflectionApproximation
open CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem discarded_bound (A B : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))(χ : Character)(Y R : ℝ),
      0<Y → 0<R →
      ‖HeckeDyadic.polynomial χ false
        (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x) Y 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Y^B/Real.sqrt Y)/R^A := by
  obtain ⟨H,D,hD,hDb⟩ := paperRadialFourier_euler_source_weighted_bound (B+A) 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨H,K*D,mul_pos hK hD,?_⟩
  intro G χ Y R hY hR
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hf : ∀x : ℝ,0<x → x^(B+A)*‖paperRadialFourier G x‖≤
      D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := by
    intro x hx
    have hh := hDb G 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) (B+A))
      (norm_nonneg _)).trans hh
  have hm := discarded_rapid_control _ A B (D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G)
    R (by positivity) hR hf
  exact (hKb χ _ ((D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G)/R^A)
    Y (by positivity) hY hm).trans_eq (by ring)

theorem discarded_negligible (xi saving L Cscale : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))(χ : Character)(Y Z : ℝ),
      1≤Z → 0<Y → Y≤Cscale*Z^L →
      ‖HeckeDyadic.polynomial χ false
        (fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x) Y 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((saving+L*(3/2))/(xi/2))
  have hsav : saving+L*(3/2)≤xi/2*(A:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : 0<xi/2)).mp hA.le
    nlinarith
  obtain ⟨H,C,hC,hbound⟩ := discarded_bound A 2 (by omega)
  refine ⟨H,C*Cscale^(3/2:ℝ),by positivity,?_⟩
  intro G χ Y Z hZ hY hYZ
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hR : 0<Z^(xi/2) := Real.rpow_pos_of_pos hz _
  have hp : Y^2/Real.sqrt Y≤Cscale^(3/2:ℝ)*Z^(L*(3/2)) := by
    rw [normalized_power_eq Y hY 2]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
    calc
      _≤(Cscale*Z^L)^(3/2:ℝ) := Real.rpow_le_rpow hY.le hYZ (by norm_num)
      _=_ := by rw [Real.mul_rpow hscale.le (by positivity),←Real.rpow_mul hz.le]
  have hd : (Z^(xi/2))^A=Z^((xi/2)*(A:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  calc
    _≤C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Y^2/Real.sqrt Y)/(Z^(xi/2))^A :=
      hbound G χ Y _ hY hR
    _≤C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        (Cscale^(3/2:ℝ)*Z^(L*(3/2)))/(Z^(xi/2))^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=(C*Cscale^(3/2:ℝ))*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        Z^(L*(3/2)-(xi/2)*(A:ℝ)) := by
      rw [hd,Real.rpow_sub hz]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

theorem deleted_discarded_negligible (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))
      (S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)(η ηi χ : Character)(Q X Z : ℝ),
      1≤Z → 0<Q → 0<X → Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X →
      let F := fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x
      (∀D∈S.powerset,Summable (fun I : SmoothIdeal S=>coefficient η ηi S D I*
        HeckeDyadic.polynomial χ false F
          (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0)) ∧
      ‖∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient η ηi S D I*
        HeckeDyadic.polynomial χ false F
          (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
          (Ideal.absNorm (∏P∈S,P):ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hCb⟩ := discarded_negligible xi saving L Cscale hxi hscale
  obtain ⟨D,hD,hDb⟩ := coefficient_column_bound epsilon hepsilon
  refine ⟨H,D*C,mul_pos hD hC,?_⟩
  intro G S hS η ηi χ Q X Z hZ hQ hX hcap
  dsimp only
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hh := hDb S hS η ηi
    (fun E I=>HeckeDyadic.polynomial χ false
      (fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x)
      (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm I.val)) 0 0)
    (C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*Z^(-saving)) (by positivity) (by
      intro E hE I
      have hy := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) I Q X (Cscale*Z^L) hQ hX hcap
      exact hCb G χ _ Z hZ hy.1 hy.2)
  exact ⟨hh.1,hh.2.trans_eq (by ring)⟩

lemma retainedSchwartz_eq (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) (hX : 0<X) :
    retainedSchwartz χ ψ G X R=
      let S := redundantSet χ.modulus ψ.modulus
      ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
        HeckeDyadic.polynomial χ.inverse false (fun x=>(retainedWeight R x:ℂ)*paperRadialFourier G x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0 := by
  unfold retainedSchwartz
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro I
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hN := subset_product_norm_pos D (fun P hP=>redundantSet_prime _ _ P
    ((Finset.mem_powerset.mp hD) hP))
  have hI := norm_pos I.val
  rw [finiteAnnularColumn_eq _ _ (reflected_decayTwo G) _ _ (by positivity)]

theorem original_split (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(G : 𝓢(ℝ,ℂ))(X R : ℝ),0<X →
        HeckeDyadic.polynomial χ false G X 0 0=
          g*(retainedSchwartz χ ψ G X R+discardedSchwartz χ ψ G X R) := by
  obtain ⟨ψ,g,hp,hnp,hg,hcap,h⟩ := original_retained_reflection χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro G X R hX
  rw [retainedSchwartz_eq χ ψ G X R hX]
  exact h G X R hX

theorem actual_original_approximation (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 →
      ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(G : 𝓢(ℝ,ℂ))(X Z : ℝ),0<X → 1≤Z →
        (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
        ‖HeckeDyadic.polynomial χ false G X 0 0-
          g*retainedSchwartz χ ψ G X (Z^(xi/2))‖≤
          C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(χ.modulus.absNorm:ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hCb⟩ := deleted_discarded_negligible xi saving L Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,hC,?_⟩
  intro χ hn
  obtain ⟨ψ,g,hp,hnp,hg,hcap,hsplit⟩ := original_split χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro G X Z hX hZ hmod
  let S := redundantSet χ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hcap' : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X := by
    have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤(χ.modulus.absNorm:ℝ) := by
      exact_mod_cast hcap
    exact hc.trans hmod
  rw [hsplit G X (Z^(xi/2)) hX,mul_add,add_sub_cancel_left,norm_mul,hg,one_mul]
  have hb := (hCb G S hS ψ ψ.inverse χ.inverse _ X Z hZ hQ hX hcap').2
  apply hb.trans
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (radical_le_original χ ψ hcap) hepsilon.le

end SevenEighths.CenteredMomentUniformReflectionApproximation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.UniformOriginalEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformOriginalEnergy
open HeckeFamily CenteredMomentUniformReflectionApproximation CenteredMomentNaturalPrimitive
open CenteredMomentOriginalReflectionEnergy

theorem actual_original_energy_to_retained (xi saving L Cscale ε : ℝ)
     (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀χ : ι→Character,
        (∀i,(χ i).residue≠1) →
        ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
        ∀(W : ι→𝓢(ℝ,ℂ))(X : ι→ℝ)(P : ι→ℂ)(D Z Rcap : ℝ),0<D → 1≤Z → 1≤Rcap →
          (∀i,0<X i) → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W i)≤D) → (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
          (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*X i) →
          (∑i,‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i‖^2)≤
            2*(∑i,‖retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))*P i‖^2)+
            C*Rcap^(2*ε)*D^2*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨H,C,hC,hb⟩ := actual_original_approximation xi saving L Cscale ε hxi hscale hε
  refine ⟨H,2*C ^2,by positivity,?_⟩
  intro ι _ χ hχ
  choose ψ G hp hnψ hG hcap happrox using fun i=>hb (χ i) (hχ i)
  refine ⟨ψ,fun i=>⟨hp i,hnψ i,hcap i⟩,?_⟩
  intro W X P D Z Rcap hD hZ hR hX hWD hmod hsource
  let B := C*D*Rcap^ε*Z^(-saving)
  have hB : 0≤B := by dsimp [B];positivity
  have herr (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0-
        G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))‖≤B := by
    apply (happrox i (W i) (X i) Z (hX i) hZ (hsource i)).trans
    dsimp [B]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hWD i) hC.le)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hmod i) hε.le)
      (by positivity) (by positivity)
  have hpoint (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i‖^2≤
      2*‖retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))*P i‖^2+B^2*(2*‖P i‖^2) := by
    have hh := norm_sq_comparison
      (HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i)
      ((G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2)))*P i)
    have he : ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i-
        (G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2)))*P i‖≤B*‖P i‖ := by
      rw [←sub_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (herr i) (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
    simp only [norm_mul,hG,one_mul] at hh
    simp only [mul_pow] at hs
    simp only [norm_mul]
    nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset ι))=>hpoint i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hBeq : B^2*2=(2*C ^2)*Rcap^(2*ε)*D^2*Z^(-2*saving) := by
    have hr0 : 0≤Rcap := by linarith
    have hz0 : 0≤Z := by linarith
    have hr : (Rcap^ε)^2=Rcap^(2*ε) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr0];congr 1;ring
    have hz : (Z^(-saving))^2=Z^(-2*saving) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hz0];congr 1;ring
    dsimp [B]
    rw [mul_pow,mul_pow,mul_pow,hr,hz]
    ring
  convert (preTransparency := .instances) hh using 1
  rw [←mul_assoc,hBeq]

end SevenEighths.CenteredMomentUniformOriginalEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dirichlet
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

variable {q : ℕ}

theorem modulus_ne_bot [NeZero q] : modulus q ≠ ⊥ := by
  simpa only [modulus, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : O) ≠ 0)

variable [NeZero q]

end SevenEighths.HeckeDirichlet

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroReflectionSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReflectionSupport
open HeckeFamily Filter CenteredMomentNaturalPrimitive EisensteinSchwartzPoisson
open CenteredMomentReflectionMass CenteredMomentNaturalRowSource
open CenteredMomentReflectionDeletion CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
local notation "O" => HeckeFamily.O

lemma naturalDualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0<X)
    (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
    (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) :
    0<naturalDualScale χ ψ X D H := by
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hN := subset_product_norm_pos D (fun P hP=>redundantSet_prime _ _ P
    (Finset.mem_powerset.mp hD hP))
  have hH := norm_pos H.val
  unfold naturalDualScale
  positivity

theorem eventually_natural_choice_range (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      ∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Z^a) D H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY → 0≤M-a+xi := by
  filter_upwards [eventually_natural_choice_geometry C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod D hD H hY n hn
  have h := hZ.2 χ ψ M a hcap hmod ((⟨D,hD⟩,H),n) hY hn
  have hz := Real.log_pos hZ.1
  have hm : 0≤(M-a+xi)*Real.log Z := h.2.1.trans h.2.2
  nlinarith

theorem eventually_natural_source_zero (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M → M+xi<a →
      (∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Z^a) D H),
        retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅) ∧
      (∀(D : Finset (Ideal O)),D∈(redundantSet χ.modulus ψ.modulus).powerset →
        ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))(η : Character)(F : ℝ→ℂ),
        finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0) ∧
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  filter_upwards [eventually_natural_choice_range C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod hfar
  have hempty (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
      (hY : 0<naturalDualScale χ ψ (Z^a) D H) :
      retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have h := hZ.2 χ ψ M a hcap hmod D hD H hY n hn
    linarith
  have hcol (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) (η : Character)(F : ℝ→ℂ) :
      finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0 := by
    have hy := naturalDualScale_pos χ ψ (Z^a) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) D hD H
    rw [finiteAnnularColumn,dif_pos hy,hempty D hD H hy]
    simp
  refine ⟨hempty,hcol,?_,?_⟩
  · intro W t
    unfold retainedOriginal
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]
  · intro G
    unfold retainedSchwartz
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]

end SevenEighths.CenteredMomentEnergyZeroReflectionSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ZeroRetainedError
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroRetainedError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalPrimitive CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyZeroReflectionSupport CenteredMomentOriginalRadialComparison
open CenteredMomentRadialPolynomialEnergy CenteredMomentEnergyState
open CenteredMomentEnergyReferenceState
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional CenteredMomentLattice
local notation "O" => HeckeFamily.O

theorem finite_original_error (xi saving Cscale epsilon : ℝ)
    (hxi : 0<xi)(hscale : 0<Cscale)(hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
      ∀{ι : Type}[Fintype ι],∀χ : ι→Character,(∀i,(χ i).residue≠1) →
      ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
      ∀(G : ι→𝓢(ℝ,ℂ))(P : ι→ℂ)(Z M along Src Rcap : ℝ),Z₀≤Z →
        M+xi<along → 0<Src → 1≤Rcap →
        (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤Src) →
        (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
        (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
        (∀i,retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))=0) ∧
        (∑i,‖polynomial (χ i) false (G i) (Z^along) 0 0*P i‖^2)≤
          C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨H,C,hC,happrox⟩:=CenteredMomentUniformOriginalEnergy.actual_original_energy_to_retained
    (xi/2) saving 0 Cscale epsilon (by positivity) hscale hepsilon
  obtain ⟨Z₁,hZ₁⟩:=eventually_atTop.mp (eventually_natural_source_zero Cscale xi hscale hxi)
  refine ⟨H,C,max 2 Z₁,hC,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro ι _ χ hχ
  obtain ⟨ψ,hψ,henergy⟩:=happrox χ hχ
  refine ⟨ψ,hψ,?_⟩
  intro G P Z M along Src Rcap hZ₀ hfar hSrc hR hGS hmod hcap
  have hZ:=hZ₁ Z ((le_max_right _ _).trans hZ₀)
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hzero(i:ι):retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))=0:=
    (hZ.2 (χ i) (ψ i) M along (hψ i).2.2 (hmod i) hfar).2.2.2 (G i)
  have hsource(i:ι):((χ i).modulus.absNorm:ℝ)≤Cscale*Z^(0:ℝ)*Z^along:=by
    simp only [Real.rpow_zero,mul_one]
    exact (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)) hscale.le)
  have hh:=henergy G (fun _=>Z^along) P Src Z Rcap hSrc hZ.1.le hR
    (fun _=>Real.rpow_pos_of_pos hz _) hGS hcap hsource
  rw [show (xi/2)/2=xi/4 by ring] at hh
  simp only [hzero,zero_mul,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,
    mul_zero,zero_add] at hh
  exact ⟨hzero,hh⟩

theorem radial_original_error_oai (xi saving Cscale epsilon : ℝ)
    (hxi : 0<xi)(hscale : 0<Cscale)(hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
      ∀(G:O→𝓢(ℝ,ℂ))(χ:O→Character)(P:O→ℂ)(omega:O→ℝ)
        (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Pbound:ℝ)(Wshort:ℝ→ℂ)
        (c d Z M along Xshort Src Rcap:ℝ),
      Z₀≤Z → 0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,‖P z‖≤Pbound) → (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → 0<Xshort →
      M+xi<along → 0<Src → 1≤Rcap →
      (∀z,keep z → H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G z)≤Src) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      radialEnergy (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K≤
        C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K := by
  obtain ⟨H,C,Z₀,hC,hZ₀,hfinite⟩:=finite_original_error xi saving Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,Z₀,hC,hZ₀,?_⟩
  intro G χ P omega keep Φ K Pbound Wshort c d Z M along Xshort Src Rcap
    hZ hK hΦ hP hχ hd hshort hXshort hfar hSrc hR hGS hmod hcap
  have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hshortsum:=single_radial_summable χ P omega Wshort c d Xshort Pbound hd hXshort
    hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  have hmem(z:↥S):keep (z:O):=(Finset.mem_filter.mp z.property).2
  obtain ⟨ψ,hψ,hf⟩:=hfinite (fun z:↥S=>χ z) (fun z=>hχ z (hmem z))
  let Q(z:↥S):ℂ:=
    (polynomial (χ z) false Wshort Xshort 0 (omega z)*P z)*
      (Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hh:=(hf (fun z:↥S=>G z) Q Z M along Src Rcap hZ hfar hSrc hR
    (fun z=>hGS z (hmem z)) (fun z=>hmod z (hmem z)) (fun z=>hcap z (hmem z))).2
  simp only [Q,←mul_assoc] at hh
  rw [finite_weighted rows keep
      (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) Φ K hΦ,
    finite_weighted rows keep
      (fun z=>polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) Φ K hΦ] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (hshortsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl))
    (by positivity))

end SevenEighths.CenteredMomentEnergyZeroRetainedError

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentEnergyZeroRetainedError.radial_original_error_oai := @OAI.SevenEighths.CenteredMomentEnergyZeroRetainedError.radial_original_error_oai
