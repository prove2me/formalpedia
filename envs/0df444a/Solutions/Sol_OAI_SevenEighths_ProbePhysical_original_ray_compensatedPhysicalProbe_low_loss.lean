-- Prove2me | solution 1 for OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_loss
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:50:07.102689+00:00
-- url     : https://prove2.me/submissions/98baff61-6be9-49eb-bf6a-a0cd7191d274

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Definitions.Def_OAIHecke78B023
import Theorems.Thm_OAI_SevenEighths_ProbePhysical_compensation_subset_common
import Theorems.Thm_OAI_SevenEighths_ProbePhysical_gaussianPhysicalFamily_remote_polynomial
import Theorems.Thm_OAI_SevenEighths_ProbePhysical_low_central_gaussian_dyad

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction
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

namespace DyadicTransfer

theorem annularCutoff_eq_zero_of_le_half (φ : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    {y : ℝ} (hy : y ≤ 1 / 2) : annularCutoff φ y = 0 := by
  have hy1 : y ≤ 1 := by linarith
  have h2y : 2 * y ≤ 1 := by linarith
  simp [annularCutoff, hsmall y hy1, hsmall (2 * y) h2y]

end DyadicTransfer

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation
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

open scoped BigOperators Classical SchwartzMap

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

open FirstPassCubeLabels

lemma weighted_schwartz_integrable (b : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  simpa using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J

end JointLogSeparation

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.QuantitativePassage
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators
namespace CompletedDyadic

theorem pow_rpow_comm (s : ℝ) (n : ℕ) : ((2:ℝ)^n)^s=((2:ℝ)^s)^n := by
  rw [←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem kernelTerm_nonneg (t s A : ℝ) (ht : 0<t) (n : ℕ) : 0≤kernelTerm t s A n := by
  unfold kernelTerm
  positivity

theorem kernelTerm_le_head (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤((2:ℝ)^s)^n := by
  rw [kernelTerm,←pow_rpow_comm]
  exact div_le_self (Real.rpow_nonneg (by positivity) _)
    (Real.one_le_rpow (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]) hA)

theorem kernelTerm_le_tail (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤t^(-A)*((2:ℝ)^(s-A))^n := by
  have hn : 0<(2:ℝ)^n := by positivity
  have htA : 0<t^A := Real.rpow_pos_of_pos ht _
  calc
    _ ≤ ((2:ℝ)^n)^s/(t*(2:ℝ)^n)^A := by
      unfold kernelTerm
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow (by positivity) (by linarith) hA)
    _ = t^(-A)*(((2:ℝ)^n)^s/((2:ℝ)^n)^A) := by
      rw [Real.mul_rpow ht.le hn.le,Real.rpow_neg ht.le]
      ring
    _ = _ := by rw [←Real.rpow_sub hn,pow_rpow_comm]

theorem ratio_lt_one (s A : ℝ) (hsA : s<A) : (2:ℝ)^(s-A)<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsA)

theorem kernel_summable (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (hsA : s<A) :
    Summable (kernelTerm t s A) := by
  have hq := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (s-A)) (ratio_lt_one s A hsA)
  exact (hq.mul_left (t^(-A))).of_nonneg_of_le (kernelTerm_nonneg t s A ht) (kernelTerm_le_tail t s A ht hA)

theorem kernel_sum_cutoff (t s A : ℝ) (ht : 0<t) (hs : 0<s) (hsA : s<A) (N : ℕ) :
    (∑'n : ℕ,kernelTerm t s A n)≤
      ((2:ℝ)^s)^N/((2:ℝ)^s-1)+t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
  have hA : 0≤A := by linarith
  have hp : 1<(2:ℝ)^s := Real.one_lt_rpow (by norm_num) hs
  have hq : (2:ℝ)^(s-A)<1 := ratio_lt_one s A hsA
  have hq0 : 0≤(2:ℝ)^(s-A) := by positivity
  have hsum := kernel_summable t s A ht hA hsA
  have hhead : (∑n∈Finset.range N,kernelTerm t s A n)≤((2:ℝ)^s)^N/((2:ℝ)^s-1) := by
    apply (Finset.sum_le_sum (fun n _ => kernelTerm_le_head t s A ht hA n)).trans
    rw [geom_sum_eq hp.ne']
    exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hp.le)
  have htail : (∑'n : ℕ,kernelTerm t s A (n+N))≤
      t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
    have hgeo := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A)*((2:ℝ)^(s-A))^N)
    have hb := Summable.tsum_le_tsum (fun n => show kernelTerm t s A (n+N)≤
      (t^(-A)*((2:ℝ)^(s-A))^N)*((2:ℝ)^(s-A))^n by
        simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using kernelTerm_le_tail t s A ht hA (n+N))
      ((summable_nat_add_iff N).mpr hsum) hgeo
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    simpa only [div_eq_mul_inv] using hb
  rw [←hsum.sum_add_tsum_nat_add N]
  exact add_le_add hhead htail

theorem kernel_sum_bound (s A : ℝ) (hs : 0<s) (hsA : s<A) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      Summable (kernelTerm t s A) ∧ (∑'n : ℕ,kernelTerm t s A n)≤C*t^(-s) := by
  let r : ℝ := (2:ℝ)^s
  let q : ℝ := (2:ℝ)^(s-A)
  have hr : 1< r := Real.one_lt_rpow (by norm_num) hs
  have hq : q<1 := ratio_lt_one s A hsA
  have hq0 : 0≤q := by dsimp [q]; positivity
  let C := r/(r-1)+1/(1-q)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  have hA : 0≤A := by linarith
  have hsum := kernel_summable t s A ht hA hsA
  refine ⟨hsum,?_⟩
  by_cases ht1 : 1≤t
  · have hg := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A))
    have hb := hsum.tsum_le_tsum (fun n => kernelTerm_le_tail t s A ht hA n) hg
    change (∑'n : ℕ,kernelTerm t s A n)≤∑'n : ℕ,t^(-A)*q^n at hb
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    calc
      _ ≤ t^(-A)/(1-q) := by simpa only [div_eq_mul_inv] using hb
      _ ≤ t^(-s)/(1-q) := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by linarith)
      _ ≤ C*t^(-s) := by
        have hp : 0≤ r/(r-1)*t^(-s) := by positivity
        calc
          _ ≤ r/(r-1)*t^(-s)+t^(-s)/(1-q) := le_add_of_nonneg_left hp
          _ = C*t^(-s) := by dsimp [C]; ring
  · have ht_le : t≤1 := le_of_not_ge ht1
    have hit : 1≤1/t := (one_le_div ht).mpr ht_le
    obtain ⟨N,hN,hN'⟩ := exists_nat_pow_near hit (by norm_num : (1:ℝ)<2)
    have hheadpow : r^(N+1)≤ r*t^(-s) := by
      change ((2:ℝ)^s)^(N+1)≤(2:ℝ)^s*t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ ((2:ℝ)/t)^s := by
          apply Real.rpow_le_rpow (by positivity) _ hs.le
          rw [pow_succ]
          calc
            _ ≤ (1/t)*2 := mul_le_mul_of_nonneg_right hN (by norm_num)
            _ = 2/t := by ring
        _ = _ := by rw [Real.div_rpow (by norm_num) ht.le,Real.rpow_neg ht.le]; ring
    have htailpow : t^(-A)*q^(N+1)≤t^(-s) := by
      change t^(-A)*((2:ℝ)^(s-A))^(N+1)≤t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ t^(-A)*(1/t)^(s-A) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hN'.le (by linarith)) (by positivity)
        _ = t^(-A)*t^(-(s-A)) := by rw [one_div,Real.inv_rpow ht.le,←Real.rpow_neg ht.le]
        _ = t^(-s) := by rw [←Real.rpow_add ht]; congr 1; ring
    have hb := kernel_sum_cutoff t s A ht hs hsA (N+1)
    change (∑'n : ℕ,kernelTerm t s A n)≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) at hb
    calc
      _ ≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) := hb
      _ ≤ (r*t^(-s))/(r-1)+t^(-s)/(1-q) := add_le_add
        (div_le_div_of_nonneg_right hheadpow (by linarith))
        (div_le_div_of_nonneg_right htailpow (by linarith))
      _ = C*t^(-s) := by dsimp [C]; ring

end CompletedDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Row
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve InitialMeanSquare ProbeCompleted

local notation "O" => ActualEisensteinCubic.O

theorem targetMonoid_norm_le_one (η : HeckeFamily.Character) (a : O) :
    ‖targetMonoid η a‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue (Ideal.Quotient.mk η.modulus a)

end SevenEighths.ProbeRow
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalNorms
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma elementNorm_mul (a b : ActualEisensteinCubic.O) :
    elementNorm (a*b)=elementNorm a*elementNorm b := by
  simp only [elementNorm,←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.TuplePrime
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma primaryTuple_norm (P : PrimeIdeal) (hP : Supported P.val) :
    elementNorm (primaryGenerator P.val)=(Ideal.absNorm P.val:ℝ) := by
  unfold elementNorm
  rw [span_primaryGenerator_of_supported P.val hP]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CanonicalSlots
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma canonicalSlotSupport_nonzero (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (a : O) (ha : a∈canonicalSlotSupport T) : a≠0 := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp ha
  exact supported_primaryGenerator_ne_zero P.val (hT P hP)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianPartition
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
namespace SevenEighths.ProbePhysical
open DyadicTransfer

lemma gaussianCutoff_small (y : ℝ) (hy : y≤1) : gaussianCutoff y=1 := by
  simp only [gaussianCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤2-y),Complex.ofReal_one]
lemma gaussianCutoff_large (y : ℝ) (hy : 2≤y) : gaussianCutoff y=0 := by
  simp only [gaussianCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 2-y≤0),Complex.ofReal_zero]
lemma gaussianAnnulus_small (y : ℝ) (hy : y≤1/2) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_le_half gaussianCutoff gaussianCutoff_small hy
lemma gaussianAnnulus_large (y : ℝ) (hy : 2≤y) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_two_le gaussianCutoff gaussianCutoff_large hy

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianFlow
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

lemma gaussianFlow_real (R : ℝ) (hR : 0<R) (s : ℝ) :
    gaussianFlow R (s:ℂ)=gaussianMellinProfile (R*Real.exp s) := by
  unfold gaussianFlow gaussianMellinProfile
  rw [←Complex.ofReal_log (mul_pos hR (Real.exp_pos _)).le,Real.log_mul hR.ne' (Real.exp_pos _).ne',Real.log_exp,
    Complex.ofReal_add]

lemma iteratedDeriv_restrict_real (f : ℂ→ℂ)
    (hf : ∀x : ℝ,AnalyticAt ℂ f (x:ℂ)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ=>f (y:ℂ)) x=iteratedDeriv n f (x:ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',iteratedDeriv_succ']
    have he : deriv (fun y : ℝ=>f (y:ℂ))=(fun y : ℝ=>deriv f (y:ℂ)) := by
      funext y
      exact (hf y).differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [he]
    exact ih (deriv f) (fun y=>(hf y).deriv)

lemma gaussianFlow_disk_bound (a L : ℝ) (_hL : 0≤L) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ∀z∈Metric.closedBall (y:ℂ) 1,‖gaussianFlow R z‖≤C*R^(-a) := by
  let c := ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖
  let B := Real.exp (a^2+1/4+|a| *(L+1))
  have hc : 0≤ c := norm_nonneg _
  have hB : 0<B := Real.exp_pos _
  refine ⟨(c+1)*B,by positivity,?_⟩
  intro R hR y hy z hz
  have hd : ‖z-(y:ℂ)‖≤1 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hzr := (Complex.abs_re_le_norm (z-(y:ℂ))).trans hd
  have hzi := (Complex.abs_im_le_norm (z-(y:ℂ))).trans hd
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hzr hzi
  have hre : |z.re|≤L+1 := by
    have h := abs_add_le (z.re-y) y
    have he : z.re-y+y=z.re := by ring
    rw [he] at h
    linarith
  have hsq : z.im^2≤1 := by nlinarith [(abs_le.mp hzi).1,(abs_le.mp hzi).2]
  have hmul : -(a*z.re)≤|a| *(L+1) := by
    calc
      _ ≤ |a*z.re| := neg_le_abs _
      _ = |a| *|z.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hre (abs_nonneg _)
  have he : (-((Real.log R:ℂ)+z)^2/4).re=(z.im^2-(Real.log R+z.re)^2)/4 := by
    simp [pow_two,Complex.mul_re]
  unfold gaussianFlow
  rw [norm_mul,Complex.norm_exp,he]
  have hb : Real.exp ((z.im^2-(Real.log R+z.re)^2)/4)≤B*R^(-a) := by
    rw [Real.rpow_def_of_pos hR,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((Real.log R+z.re)/2-a)]
  calc
    _ ≤ c*(B*R^(-a)) := mul_le_mul_of_nonneg_left hb hc
    _ ≤ (c+1)*B*R^(-a) := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]

lemma gaussianFlow_derivative_bound (a L : ℝ) (hL : 0≤L) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ‖iteratedDeriv n (fun s : ℝ=>gaussianFlow R (s:ℂ)) y‖≤C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianFlow_disk_bound a L hL
  refine ⟨(n.factorial:ℝ)*B,by positivity,?_⟩
  intro R hR y hy
  rw [iteratedDeriv_restrict_real _ (fun x=>gaussianFlow_analytic R (x:ℂ)) n y]
  have hf : Differentiable ℂ (gaussianFlow R) := fun z=>(gaussianFlow_analytic R z).differentiableAt
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl
    (fun z hz=>hbound R hR y hy z (Metric.sphere_subset_closedBall hz))
  simpa only [one_pow,div_one,mul_assoc] using h

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianLogWindow
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open Filter Set MeasureTheory
namespace SevenEighths.ProbePhysical

lemma gaussianLogWindow_derivative_outside (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hbox : ∀s,V s≠0→|s|≤L) (R y : ℝ) (hy : L < |y|) (n : ℕ) :
    iteratedDeriv n (gaussianLogWindow V hV R) y=0 := by
  have he : (gaussianLogWindow V hV R:ℝ→ℂ)=ᶠ[𝓝 y](fun _=>0) := by
    have hu : {x : ℝ | L < |x|}∈𝓝 y := (isOpen_lt continuous_const continuous_abs).mem_nhds hy
    filter_upwards [hu] with x hx
    have hv : V x=0 := by by_contra h; exact (not_lt_of_ge (hbox x h)) hx
    simp only [gaussianLogWindow_apply,hv,zero_mul]
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianLogWindow_derivative_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ‖iteratedDeriv n (gaussianLogWindow V hV R) y‖≤C*R^(-a) := by
  choose B hB hbound using fun i : ℕ=>gaussianFlow_derivative_bound a L hL i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i V
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤A i := apply_nonneg _ _
  have hC : 0≤C := Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro R hR y hy
  change ‖iteratedDeriv n (fun s : ℝ=>V s*gaussianFlow R (s:ℂ)) y‖≤_
  rw [iteratedDeriv_fun_mul (f:=(V:ℝ→ℂ)) (g:=fun s : ℝ=>gaussianFlow R (s:ℂ))
    (V.smooth'.contDiffAt.of_le (by simp))
    ((gaussianFlow_real_smooth R).contDiffAt.of_le (by simp))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i V y*
        iteratedDeriv (n-i) (fun s : ℝ=>gaussianFlow R (s:ℂ)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*R^(-a)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hv : ‖iteratedDeriv i V y‖≤A i := by
        simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm' ℝ 0 i V y
      exact mul_le_mul (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _))
        (hbound _ R hR y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*R^(-a) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*R^(-a) := by nlinarith [Real.rpow_pos_of_pos hR (-a)]

theorem gaussianLogWindow_seminorm (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (hbox : ∀s,V s≠0→|s|≤L) (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
      SchwartzMap.seminorm ℝ k n (gaussianLogWindow V hV R)≤C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianLogWindow_derivative_bound V hV L hL a n
  refine ⟨(1+L^k)*B,by positivity,?_⟩
  intro R hR
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  by_cases hy : |y|≤L
  · calc
      _ ≤ L^k*(B*R^(-a)) := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy k)
        (hbound R hR y hy) (norm_nonneg _) (pow_nonneg hL _)
      _ ≤ _ := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]
  · rw [gaussianLogWindow_derivative_outside V hV L hbox R y (lt_of_not_ge hy) n,norm_zero,mul_zero]
    positivity

theorem gaussianLogWindow_fourier_moment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (hbox : ∀s,V s≠0→|s|≤L) (a : ℝ) (J : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
      (∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤C*R^(-a) := by
  let p := (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower
  let K := J+p
  choose B hB hb using fun q : ℕ×ℕ=>gaussianLogWindow_seminorm V hV L hL hbox a q.1 q.2
  let C := (∑i∈Finset.range (K+1),(B (0,i)+B (p,i)))+1
  have hC : 0<C := by
    have hh : 0≤∑i∈Finset.range (K+1),(B (0,i)+B (p,i)) :=
      Finset.sum_nonneg (fun i _=>add_nonneg (hB _).le (hB _).le)
    dsimp only [C]; linarith
  let D := (2:ℝ)^J*(FourierBridge.coefficientMomentBound 0 C+FourierBridge.coefficientMomentBound J C)
  have hD : 0≤D := mul_nonneg (by positivity)
    (add_nonneg (FourierBridge.coefficientMomentBound_nonneg _ _ hC.le)
      (FourierBridge.coefficientMomentBound_nonneg _ _ hC.le))
  refine ⟨D+1,by positivity,?_⟩
  intro R hR
  have hcancel : R^a*R^(-a)=1 := by rw [←Real.rpow_add hR]; simp
  have hsource (i : ℕ) (hi : i≤J+(MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower) :
      R^a*(SchwartzMap.seminorm ℝ 0 i (gaussianLogWindow V hV R)+
        SchwartzMap.seminorm ℝ p i (gaussianLogWindow V hV R))≤C := by
    have hbi : B (0,i)+B (p,i)≤C := by
      have hh := Finset.single_le_sum (s:=Finset.range (K+1)) (a:=i)
        (f:=fun i=>B (0,i)+B (p,i))
        (fun i _=>add_nonneg (hB _).le (hB _).le) (Finset.mem_range.mpr (by dsimp only [K,p]; omega))
      dsimp only [C]; linarith
    calc
      _ ≤ R^a*(B (0,i)*R^(-a)+B (p,i)*R^(-a)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hb (0,i) R hR) (hb (p,i) R hR)) (by positivity)
      _ = B (0,i)+B (p,i) := by rw [←add_mul]; calc
        _=(B (0,i)+B (p,i))*(R^a*R^(-a)) := by ring
        _=_ := by rw [hcancel,mul_one]
      _ ≤ C := hbi
  have hh := FourierBridge.uniform_fourier_one_plus_moment (gaussianLogWindow V hV R) J
    (R^a) C (by positivity) hC.le hsource
  change R^a*(∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤D at hh
  have hp := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hR (-a)).le
  have hc' : R^(-a)*R^a=1 := by rw [mul_comm,hcancel]
  rw [←mul_assoc,hc',one_mul] at hp
  exact hp.trans (by nlinarith [Real.rpow_pos_of_pos hR (-a)])

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianCoupled
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge LocalLogFourier
namespace SevenEighths.ProbePhysical

lemma gaussianLogWindow_eq_positive (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R : ℝ) (hR : 0<R) : gaussianLogWindow V hV R=
      positiveLogProfile V gaussianMellinProfile R hV V.smooth' gaussianProfile_positive_smooth hR := by
  ext s
  simp only [gaussianLogWindow_apply,positiveLogProfile_apply,gaussianFlow_real R hR]

theorem gaussian_coupled_separation {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a y : ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) (hR : 0<R)
    (hactive : (∏i,W i (y i))≠0→V (∑i,a i*y i)=1) :
    (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
      ∫t : ℝ,(∏i,W i (y i)*logPhase t (a i*y i))*gaussianJointDensity V hV R t := by
  have hh := coupled_positive_log_separation W gaussianMellinProfile V R a y hV V.smooth'
    gaussianProfile_positive_smooth hR hactive
  rw [←gaussianLogWindow_eq_positive V hV R hR] at hh
  exact hh

theorem gaussian_coupled_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i y≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0<R→∀y : ι→ℝ,
        (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
          ∫t : ℝ,(∏i,W i (y i)*logPhase t (a i*y i))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) := by
  let T := ∑i,|a i| *M i
  have hT : 0≤T := Finset.sum_nonneg (fun i _=>mul_nonneg (abs_nonneg _) (hM i))
  obtain ⟨φ,hφc,hφs,hφone,hφsupp,_⟩ := FourierBridge.exists_complex_smooth_cutoff T hT
  let V : SchwartzMap ℝ ℂ := hφc.toSchwartzMap hφs
  have hV : HasCompactSupport (V:ℝ→ℂ) := hφc
  have hbox : ∀s,V s≠0→|s|≤T+1 := by
    intro s hs
    have hh := hφsupp (subset_tsupport φ hs)
    exact abs_le.mpr hh
  refine ⟨V,hV,?_,?_⟩
  · intro R hR y
    apply gaussian_coupled_separation W a y V hV R hR
    exact FourierBridge.coupled_cutoff_active W φ a y M hwindow (by simpa only [T] using hφone)
  · intro A J
    obtain ⟨C,hC,hbound⟩ := gaussianLogWindow_fourier_moment V hV (T+1) (by linarith) hbox A J
    refine ⟨C,hC,?_⟩
    intro R hR
    exact ⟨JointLogSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV R) J,hbound R hR⟩

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianSlots
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical

lemma gaussianSlot_argument {ι : Type*} [Fintype ι] (x : ℝ) (hx : 0<x) (q : ι→ℝ) (hq : ∀i,0<q i) :
    Real.exp (∑i : Option ι,gaussianSlotSlope i*gaussianSlotPoint x q i)=x/(∏i,q i) := by
  simp only [Fintype.sum_option,gaussianSlotSlope,gaussianSlotPoint,one_mul,neg_one_mul]
  rw [Real.exp_add,Real.exp_sum,Real.exp_log hx]
  simp_rw [Real.exp_neg,Real.exp_log (hq _)]
  rw [Finset.prod_inv_distrib]
  rfl

lemma logPhase_neg_argument (t y : ℝ) : logPhase t (-y)=logPhase (-t) y := by
  unfold logPhase
  congr 1
  push_cast
  ring

lemma gaussianFixedWindow_Vstar_twist (t x : ℝ) (hx : 0<x) :
    Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x=
      gaussianAnnulus x*logPhase t (Real.log x) := by
  have hs : (Real.sqrt x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  unfold Vstar CompletedHeight.normTwistedSource gaussianFixedWindow
  field_simp

lemma gaussianAnnulus_log_support (y : ℝ) (hy : gaussianAnnulus (Real.exp y)≠0) :
    |y|≤|Real.log (1/2)|+|Real.log 2|+1 := by
  have hlo : (1/2:ℝ)<Real.exp y := by
    by_contra h; exact hy (gaussianAnnulus_small _ (le_of_not_gt h))
  have hhi : Real.exp y<2 := by
    by_contra h; exact hy (gaussianAnnulus_large _ (le_of_not_gt h))
  have hl : Real.log (1/2)≤y := by simpa using Real.log_le_log (by norm_num : (0:ℝ)<1/2) hlo.le
  have hh : y≤Real.log 2 := by simpa using Real.log_le_log (Real.exp_pos y) hhi.le
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log (1/2)); have := abs_nonneg (Real.log 2); linarith
  · have := le_abs_self (Real.log 2); have := abs_nonneg (Real.log (1/2)); linarith

theorem gaussian_selected_slot_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
        gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
          ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
            (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) := by
  let M' : Option ι→ℝ := fun o=>match o with
    | none => |Real.log (1/2)|+|Real.log 2|+1
    | some i => M i
  have hM' : ∀o,0≤M' o := by intro o; cases o with
    | none => dsimp [M']; positivity
    | some i => exact hM i
  have hW : ∀o y,gaussianSlotWindow W o y≠0→|y|≤M' o := by
    intro o y
    cases o with
    | none => exact gaussianAnnulus_log_support y
    | some i => exact hwindow i y
  obtain ⟨V,hV,hsep,hbound⟩ := gaussian_coupled_family (gaussianSlotWindow W) gaussianSlotSlope M' hM' hW
  refine ⟨V,hV,?_,hbound⟩
  intro R hR x hx q hq
  have hh := hsep R hR (gaussianSlotPoint x q)
  rw [gaussianSlot_argument x hx q hq] at hh
  simp only [Fintype.prod_option,gaussianSlotWindow,gaussianSlotPoint,Real.exp_log hx] at hh
  simp_rw [Real.exp_log (hq _)] at hh
  rw [show R*(x/∏i,q i)=R*x/(∏i,q i) by ring] at hh
  rw [hh]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [gaussianFixedWindow_Vstar_twist t x hx]
  simp only [gaussianSlotSlope,one_mul,neg_one_mul,logPhase_neg_argument]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianDensityBudget
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

lemma gaussianJointMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : 0≤gaussianJointMoment V hV J R := by
  apply integral_nonneg
  intro t
  positivity

lemma gaussianJointMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (A : ℝ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianJointMoment V hV J R≤C*R^(-A) := by
  obtain ⟨L,hL,hbox⟩ := hV.isBounded.exists_pos_norm_le
  have hb : ∀s,V s≠0→|s|≤L := by
    intro s hs
    simpa only [Real.norm_eq_abs] using hbox s (subset_tsupport V hs)
  exact gaussianLogWindow_fourier_moment V hV L hL.le hb A J

lemma gaussianJointMoment_polynomial_decay (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianJointMoment V hV J R≤C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianJointMoment_power_bound V hV J 0
  obtain ⟨C,hC,hdecay⟩ := gaussianJointMoment_power_bound V hV J (N:ℝ)
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro R hR
  have hden : 0<(1+R)^N := pow_pos (by linarith) _
  by_cases hr1 : R≤1
  · have hh := hzero R hR
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay R hR
    rw [Real.rpow_neg hR.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2*R)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hm := mul_le_mul_of_nonneg_left hp (show 0≤C*(R^N)⁻¹ by positivity)
    rw [mul_pow] at hm
    have hn : R^N≠0 := ne_of_gt (pow_pos hR _)
    have he : (C*(R^N)⁻¹)*((2:ℝ)^N*R^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianJointMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianJointMoment_polynomial_decay V hV J N
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound ((2:ℝ)^j/Z) (div_pos (by positivity) hZ))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianJointMoment_nonneg V hV J _)
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianCompensation
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma slotProduct_nonzero {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    slotProduct p J≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)

lemma slotProduct_norm_pos {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    0<elementNorm (slotProduct p J) := physicalElementNorm_pos _ (slotProduct_nonzero p hp J)

lemma compensatedTuple_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (X Y Z : ℝ) :
    compensatedTuple η C W0 W1 p X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,compensationSubsetProbe η C W0 W1 p J X Y Z := rfl

lemma compensatedPhysicalProbe_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slotPrimes : Fin K→Finset O)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,
        ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
          (∏i,W i (elementNorm (p i).val/P i))*
            compensationSubsetProbe η C W0 W1 (fun i=>(p i).val) J X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [compensatedTuple_eq_subsets,Finset.mul_sum]
  exact Finset.sum_comm

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianCommon
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

theorem compensatedPhysicalProbe_common_gaussian {K : ℕ}
    (W : Fin K→ℝ→ℂ) (M : Fin K→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : Finset (Fin K)→SchwartzMap ℝ ℂ,
    ∃hV : ∀A,HasCompactSupport (V A:ℝ→ℂ),
      (∀N : ℕ,∀s : ℝ,0<s→∃B : ℝ,0<B ∧
        ∀A : Finset (Fin K),∀Z : ℝ,0<Z→
          Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z)) ∧
          (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z))≤B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→HasCompactSupport W1→
        ∀slotPrimes : Fin K→Finset O,(∀i a,a∈slotPrimes i→a≠0)→
        ∀P : Fin K→ℝ,(∀i,0<P i)→∀X Y Z : ℝ,0<X→0<Y→0<Z→
          compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
          ∑A∈(Finset.univ : Finset (Fin K)).powerset,
            ∑'j : ℕ,∫t : ℝ,
              (∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
                compensationSubsetWeight η W P (fun i=>(p i).val) A*
                  compensationRowTest η C W0 W1 (fun i=>(p i).val) A X Y ((2:ℝ)^j) t*
                    selectedSlotFactor W P (fun i=>(p i).val) A t)*
                      gaussianJointDensity (V A) (hV A) ((2:ℝ)^j/(Z*∏i∈Finset.univ\A,P i)) t) := by
  choose V hV hsep hbound using fun A : Finset (Fin K)=>
    gaussian_selected_slot_family (fun i : SelectedSlot A=>W i.val)
      (fun i : SelectedSlot A=>M i.val) (fun i=>hM i.val) (fun i=>hwindow i.val)
  refine ⟨V,hV,?_,?_⟩
  · intro N s hs
    choose B hB hb using fun A : Finset (Fin K)=>gaussianJointMoment_summed (V A) (hV A) N s hs
    let B0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,B A)+1
    have hB0 : 0<B0 := by
      have hh : 0≤∑A∈(Finset.univ : Finset (Fin K)).powerset,B A :=
        Finset.sum_nonneg (fun A _=>(hB A).le)
      dsimp only [B0]
      linarith
    refine ⟨B0,hB0,?_⟩
    intro A Z hZ
    obtain ⟨hsm,hbd⟩ := hb A Z hZ
    refine ⟨hsm,hbd.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le s)
    have hm : A∈(Finset.univ : Finset (Fin K)).powerset := Finset.mem_powerset.mpr (Finset.subset_univ A)
    have hh := Finset.single_le_sum (fun A _=>(hB A).le) hm
    dsimp only [B0]
    linarith
  · intro η C W0 W1 hW0 hW1 slotPrimes hp P hP X Y Z hX hY hZ
    rw [compensatedPhysicalProbe_eq_subsets]
    apply Finset.sum_congr rfl
    intro A hA
    exact compensation_subset_common A W (V A) (hV A) (hsep A) η C W0 W1 hW0 hW1 Finset.univ
      (fun p : ((i : Fin K)→{a : O // a∈slotPrimes i})=>fun i=>(p i).val)
      (fun p _ i=>hp i (p i).val (p i).property) P hP X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowActualIdealLists
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowPrimeIdealList_prime (T : Finset PrimeIdeal) (I : Id) (hI : I∈lowPrimeIdealList T) : Prime I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact P.property

lemma lowPrimeIdealList_norm (T : Finset PrimeIdeal) (H : ℝ)
    (hT : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤H) (I : Id) (hI : I∈lowPrimeIdealList T) :
    (Ideal.absNorm I:ℝ)≤H := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowSlotScales
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma elementNorm_finset_prod {ι : Type*} (F : Finset ι) (p : ι→O) :
    elementNorm (∏i∈F,p i)=∏i∈F,elementNorm (p i) := by
  induction F using Finset.induction_on with
  | empty => simp [elementNorm_one]
  | @insert i F hi ih => simp only [Finset.prod_insert hi,elementNorm_mul,ih]

lemma lowUnselectedProduct_norm_bound {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b Z : ℝ) (hb : 1≤b) (hZ : 1≤Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤b^K*Z^(1/6:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤1/6 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)).trans hsum
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤b^K*Z^(1/6:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass
namespace OAI

namespace SevenEighths.PNT.AnnularPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter MeasureTheory
open SevenEighths.IdealMangoldt SevenEighths.PNT.IdealPrimeMass
open scoped BigOperators Classical Topology ContDiff

noncomputable section

theorem norm_bounds_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    x * a < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ x * b := by
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  exact ⟨(Nat.floor_lt (mul_nonneg hx.le ha)).mp h.2.2.1,
    (Nat.le_floor_iff (mul_nonneg hx.le (ha.trans hab))).mp h.2.2.2⟩

end

end SevenEighths.PNT.AnnularPrimeMass

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RaySlots
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PNT.AnnularPrimeMass
open PrincipalSignalComparison ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

theorem pool_norm_bounds (C : Set Id) (S : Finset Id) {a b x : ℝ}
    (ha : 0≤a) (hab : a≤b) (hx : 0<x) (P : PrimeIdeal) (hP : P∈pool C S a b x) :
    x*a<(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤x*b :=
  norm_bounds_of_mem_annularPrimeIdeals ha hab hx
    (Finset.mem_sdiff.mp (Finset.mem_subtype.mp hP)).1

variable (M : Id) [NeZero M]
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolGood
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical CanonicalQuadraticSieve PrincipalSignalComparison
local notation "Id" => Ideal HeckeFamily.O

theorem pool_supported (C : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b x : ℝ) (P : PrimeIdeal) (hP : P∈pool C S a b x) : Supported P.val :=
  outside_prime_supported S hS.bad P ((mem_pool C S a b x P).mp hP).2.2.2

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowLength_sum {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K)) :
    lowUnselectedLength ell J+lowSelectedLength ell J=∑i,ell i := by
  rw [lowUnselectedLength,lowSelectedLength,Finset.sum_coe_sort]
  exact Finset.sum_add_sum_compl J ell

lemma lowLength_bounds {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤1/6 ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤1/6-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma lowPhysicalScale_source (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)=
      elementNorm C.generator*Z^(5/6:ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(17/48:ℝ)*Z^(23/48:ℝ)=Z^(5/6:ℝ) := by rw [←Real.rpow_add hZ];norm_num
  rw [←he]
  ring

lemma lowSelectedScale_product {K : ℕ} (ell : Fin K→ℝ) (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0<Z) :
    (∏i∈Finset.univ\J,Z^(ell i))=Z^(lowSelectedLength ell J) := by
  rw [lowSelectedLength,Finset.sum_coe_sort,Real.rpow_sum_of_pos hZ]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowCentralGeometry
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

lemma lowCentral_ratio_bounds (Z T ell ε : ℝ) (hZ : 0<Z)
    (hlo : Z^(-ε/2)≤T/Z^(1+ell)) (hhi : T/Z^(1+ell)≤Z^(ε/2)) :
    Z^(1+ell-ε/2)≤T ∧ T≤Z^(1+ell+ε/2) := by
  constructor
  · have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hlo
    convert (preTransparency := .instances) hh using 1
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  · have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hhi
    convert (preTransparency := .instances) hh using 1
    rw [←Real.rpow_add hZ]
    congr 1
    ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowRemoteMass
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma canonicalSlot_count (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (H : ℝ) (hH : 1≤H) (hnorm : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤H) :
    ((canonicalSlotSupport T).card:ℝ)≤128*H := by
  have hh := DescentFiberCost.finite_ideal_count_real (lowPrimeIdealList T) H hH
    (fun I hI=>(lowPrimeIdealList_prime T I hI).ne_zero) (lowPrimeIdealList_norm T H hnorm)
  have he := Fintype.card_congr (canonicalSlotEquiv T hT)
  simp only [Fintype.card_coe] at he
  rw [lowPrimeIdealList,Finset.card_image_of_injective _ Subtype.val_injective,he] at hh
  exact hh

lemma canonicalTuple_count {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (b Z : ℝ) (hZ : 1≤Z)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i)) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤(128*max 1 b)^K*Z^(1/6:ℝ) := by
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _≤∏i,128*(max 1 b*Z^(ell i)) := by
      apply Finset.prod_le_prod (fun i _=>Nat.cast_nonneg _)
      intro i hi
      simp only [Fintype.card_coe]
      apply canonicalSlot_count _ (hT i) _
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i)))
      intro P hP
      exact (hnorm i P hP).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _=(128*max 1 b)^K*Z^(∑i,ell i) := by
      simp_rw [←mul_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)

lemma slotProduct_norm_ge_one {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    1≤elementNorm (slotProduct p J) := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr (slotProduct_nonzero p hp J)))

lemma compensationSubsetWeight_norm_le_one {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) (Y : Fin K→ℝ)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    ‖compensationSubsetWeight η W Y p J‖≤1 := by
  rw [compensationSubsetWeight,norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) _).trans _
  · rw [compensationSubsetCoefficient,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (slotProduct_norm_pos p hp J).le _),norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos (slotProduct_norm_ge_one p hp J) (by norm_num))).trans (ProbeRow.targetMonoid_norm_le_one η _)
  · rw [norm_prod]
    exact Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun i _=>hW i _)

lemma compensation_scale_mass_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b Z : ℝ) (hZ : 1≤Z) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=>compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=>Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C (Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^(5/6:ℝ) := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=>norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun (i : SelectedSlot J) _=>hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [lowPhysicalScale_source C Z _ hz]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=>hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0≤elementNorm C.generator*Z^(5/6:ℝ) by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*(Z^(1/6:ℝ)*Z^(5/6:ℝ)) := by ring
    _=_ := by rw [←Real.rpow_add hz];norm_num

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowGaussianDyad
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowCommonDyad_eq_family {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R : ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) :
    lowCommonDyad η C W0 W1 slots W Yp J X Y U R V hV=
    gaussianPhysicalFamilyIntegral η C W0 W1 (Finset.univ : Finset (∀i,slots i))
      (fun p=>compensationSubsetWeight η W Yp (fun i=>(p i).val) J)
      (fun p=>Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
      (fun p=>X/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Y/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Yp i.val) V hV U R := rfl

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowGaussianRemote
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma slotProduct_subtype {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    slotProduct p J=∏i : J,p i.val := by rw [Finset.prod_coe_sort];rfl

lemma eventually_low_physical_scales {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (b : ℝ) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
      ∀(slots : Fin K→Finset O),(∀i x,x∈slots i→x≠0)→
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(p : ∀i,slots i),
      1≤Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) ∧
      1≤Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<(3/16:ℝ) by norm_num)).eventually
      (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro slots hn hnorm J p
  have hl : 0<elementNorm (slotProduct (fun i=>(p i).val) J) :=
    slotProduct_norm_pos _ (fun i=>hn i _ (p i).property) J
  have hb := lowUnselectedProduct_norm_bound ell hell hsum (max 1 b) Z (le_max_left _ _) hZ.le
    slots (fun i n hm=>(hnorm i n hm).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    J (fun i=>p i.val)
  rw [←slotProduct_subtype (fun i=>(p i).val) J] at hb
  have hLX : elementNorm (slotProduct (fun i=>(p i).val) J)≤Z^(17/48:ℝ) := by
    apply hb.trans
    calc
      _≤Z^(3/16:ℝ)*Z^(1/6:ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];norm_num
  constructor
  · exact (one_le_div hl).mpr hLX
  · exact (one_le_div hl).mpr (hLX.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))

lemma low_remote_power (Z ell ε : ℝ) (N : ℕ) (hZ : 1≤Z) (hell : ell≤1/6)
    (hN : 13/3≤(ε/2)*(N:ℝ)) :
    Z*(Z^(1+ell))^2/(Z^(ε/2))^N≤Z^(-1:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsq : (Z^(1+ell))^2=Z^(2*(1+ell)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    congr 1
    push_cast
    ring
  have hn : (Z^(ε/2))^N=Z^((ε/2)*(N:ℝ)) := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  rw [hsq,hn,show Z*Z^(2*(1+ell))=Z^(1+2*(1+ell)) by rw [Real.rpow_add hz,Real.rpow_one],←Real.rpow_sub hz]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem low_remote_gaussian_dyads (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b ε : ℝ) (hε : 0<ε) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(η : HeckeFamily.Character)(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖ else 0
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(-1:ℝ) := by
  have hep : 0<ε/2 := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt ((13/3:ℝ)/(ε/2))
  have hN' : (13/3:ℝ)≤(ε/2)*(N:ℝ) := by
    have hh := (div_lt_iff₀ hep).mp hN
    nlinarith
  obtain ⟨Cg,hCg,he⟩ := gaussianPhysicalFamily_remote_polynomial V hV N
    a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg*(q*(128*max 1 b)^K)
  have hq : 0<q := calibration_elementNorm_pos _
  refine ⟨C0,by dsimp [C0];positivity,?_⟩
  filter_upwards [eventually_low_physical_scales ell hell hsum b] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro η T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈canonicalSlotSupport (T i)→elementNorm n≤b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hs := hZ.2 _ hslots hnormE J
  have hh := he η S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1 (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
    (fun p=>compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
    (fun p=>Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
    (fun p=>Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p=>Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p _=>(hs p).1) (fun p _=>(hs p).2)
    (fun i : SelectedSlot J=>W i.val) (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))
    (Z^(1+lowSelectedLength ell J)) (Z^(ε/2)) (by positivity) (Real.one_le_rpow hZ.1.le hep.le)
  simp only [←lowCommonDyad_eq_family] at hh
  refine ⟨?_,?_⟩
  · convert (preTransparency := .instances) hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only [ite_true, ite_false]
  · have hhFinal := hh.2.trans (show _≤C0*Z^(-1:ℝ) from by
      have hm := compensation_scale_mass_bound η (calibrationForSet S hS) ell hell hsum b Z hZ.1.le T hT hnorm J W hW
      calc
        _≤Cg*((q*(128*max 1 b)^K)*Z)*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N := by gcongr
        _=C0*(Z*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N) := by dsimp [C0];ring
        _≤_ := mul_le_mul_of_nonneg_left (low_remote_power Z (lowSelectedLength ell J) ε N hZ.1.le
          (by have hb := lowLength_bounds ell hell hsum J;linarith) hN') (by dsimp [C0];positivity))
    convert (preTransparency := .instances) hhFinal using 1
    apply tsum_congr
    intro j
    split_ifs with h <;> simp_all only [ite_true, ite_false]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowGaussianCentral
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma not_lowRemote_bounds (Z ell ε U : ℝ) (hZ : 0<Z)
    (h : ¬lowRemote Z ell ε U) :
    Z^(1+ell-ε/2)≤U ∧ U≤Z^(1+ell+ε/2) := by
  simp only [lowRemote,not_or,not_le] at h
  apply lowCentral_ratio_bounds Z U ell ε hZ
  · have he : Z^(-ε/2)=(Z^(ε/2))⁻¹ := by
      rw [show -ε/2=-(ε/2) by ring,Real.rpow_neg hZ.le]
    rw [he]
    exact h.1.le
  · exact h.2.le

theorem low_central_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(3/16+256*ε) := by
  obtain ⟨degree,C,hC,he⟩ := low_central_gaussian_dyad η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  obtain ⟨Cm,hCm,hm⟩ := gaussianJointMoment_summed V hV degree ε hε
  refine ⟨C*Cm,mul_pos hC hCm,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  let R := Z^(1+lowSelectedLength ell J)
  let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
    ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
      W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j) R V hV‖
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  obtain ⟨hsm,hmb⟩ := hm R (by dsimp [R];positivity)
  have hb (j : ℕ) : f j≤(C*Z^(3/16+254*ε))*
      (((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := by
    dsimp only [f]
    split_ifs with hj
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
    · obtain ⟨hlo,hhi⟩ := not_lowRemote_bounds Z (lowSelectedLength ell J) ε ((2:ℝ)^j) hz hj
      apply (hZ.2 T hT hout hdis hnorm J ((2:ℝ)^j) (by positivity) hlo hhi W hW V hV).trans
      have hp : 1≤((2:ℝ)^j)^ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp
  have hn (j : ℕ) : 0≤f j := by dsimp [f];split_ifs <;>positivity
  have hsumf := Summable.of_nonneg_of_le hn hb (hsm.mul_left (C*Z^(3/16+254*ε)))
  refine ⟨hsumf,?_⟩
  calc
    _≤∑'j : ℕ,(C*Z^(3/16+254*ε))*(((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) :=
      hsumf.tsum_le_tsum hb (hsm.mul_left _)
    _=(C*Z^(3/16+254*ε))*(∑'j : ℕ,((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := tsum_mul_left
    _≤(C*Z^(3/16+254*ε))*(Cm*R^ε) := mul_le_mul_of_nonneg_left hmb (by positivity)
    _≤_ := by
      dsimp only [R]
      rw [←Real.rpow_mul hz.le]
      calc
        _=(C*Cm)*(Z^(3/16+254*ε)*Z^((1+lowSelectedLength ell J)*ε)) := by ring
        _≤_ := by
          rw [←Real.rpow_add hz]
          apply mul_le_mul_of_nonneg_left _ (mul_pos hC hCm).le
          have hh := lowLength_bounds ell hell hsum J
          exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by nlinarith)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowGaussianSum
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_dyad_norm_split (f : ℕ→ℂ) (p : ℕ→Prop) [DecidablePred p]
    (hc : Summable (fun j=>if p j then 0 else ‖f j‖))
    (hr : Summable (fun j=>if p j then ‖f j‖ else 0)) :
    Summable f ∧ ‖∑'j,f j‖≤(∑'j,if p j then 0 else ‖f j‖)+(∑'j,if p j then ‖f j‖ else 0) := by
  have he (j : ℕ) : ‖f j‖=(if p j then 0 else ‖f j‖)+(if p j then ‖f j‖ else 0) := by
    split_ifs <;>ring
  have hn : Summable (fun j=>‖f j‖) := (hc.add hr).congr (fun j=>(he j).symm)
  refine ⟨hn.of_norm,?_⟩
  apply (norm_tsum_le_tsum_norm hn).trans_eq
  exact (tsum_congr he).trans (hc.tsum_add hr)

theorem low_all_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^(ell i)) J (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV
      Summable f ∧ ‖∑'j : ℕ,f j‖≤C*Z^(3/16+256*ε) := by
  obtain ⟨Cc,hCc,hcentral⟩ := low_central_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 V hV W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1 hW0 hW1 hW0s hW1s hWB1
  obtain ⟨Cr,hCr,hremote⟩ := low_remote_gaussian_dyads S hS ell hell hsum b ε hε V hV
    W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1 hW0 hW1 hWB0 hWB1
  refine ⟨Cc+Cr,add_pos hCc hCr,?_⟩
  filter_upwards [hcentral,hremote] with Z hc hr
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  have hc' := hc.2 T hT hout hdis hnorm J W hW
  have hr' := hr.2 η T hT (fun i P hP=>(hnorm i P hP).2) J W hW
  dsimp only at hc' hr' ⊢
  have hh := low_dyad_norm_split _ (fun j=>lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j)) hc'.1 hr'.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp : Z^(-1:ℝ)≤Z^(3/16+256*ε) := Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith)
  calc
    _≤Cc*Z^(3/16+256*ε)+Cr*Z^(-1:ℝ) := add_le_add hc'.2 hr'.2
    _≤Cc*Z^(3/16+256*ε)+Cr*Z^(3/16+256*ε) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolDisjoint
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical
local notation "Id" => Ideal HeckeFamily.O

lemma annular_power_separation (a b r s : ℝ) (ha : 0<a) (hrs : r<s) :
    ∀ᶠZ : ℝ in atTop,b*Z^r<a*Z^s := by
  have hh := (tendsto_rpow_atTop (show 0<s-r by linarith)).eventually (eventually_gt_atTop (b/a))
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  have ht : b<a*Z^(s-r) := by
    have h := (div_lt_iff₀ ha).mp hZ
    nlinarith
  have hp : 0<Z^r := Real.rpow_pos_of_pos hZ0 _
  calc
    b*Z^r < (a*Z^(s-r))*Z^r := mul_lt_mul_of_pos_right ht hp
    _=a*Z^s := by rw [mul_assoc,←Real.rpow_add hZ0];congr 1;congr 1;ring

theorem power_pools_eventually_disjoint {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀i j, i≠j→Disjoint (pool C S (a i) (b i) (Z^(ell i)))
      (pool C S (a j) (b j) (Z^(ell j))) := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i=j
  · exact Filter.Eventually.of_forall (fun Z hn=>(hn hij).elim)
  have hne : ell i≠ell j := fun h=>hij (hell h)
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · filter_upwards [annular_power_separation (a j) (b i) (ell i) (ell j) (ha j) hlt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith
  · filter_upwards [annular_power_separation (a i) (b j) (ell j) (ell i) (ha i) hgt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowCommonBound
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_window_log_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (y : ℝ) (hy : W (Real.exp y)≠0) :
    |y|≤|Real.log a|+|Real.log b| := by
  have hs := hW hy
  have hlo := Real.log_le_log ha hs.1
  have hhi := Real.log_le_log (Real.exp_pos y) hs.2
  rw [Real.log_exp] at hlo hhi
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)],
    by linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]⟩

theorem compensatedPhysicalProbe_low (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
      ‖compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
        (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i))
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤C*Z^(3/16+256*ε) := by
  obtain ⟨V,hV,hbudget,hidentity⟩ := compensatedPhysicalProbe_common_gaussian W
    (fun _=>|Real.log a|+|Real.log b|) (fun _=>by positivity)
    (fun i=>low_window_log_support (W i) a b ha (hW i))
  choose C hC he using fun A : Finset (Fin K)=>low_all_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 (V A) (hV A) W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  let C0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,C A)+1
  have hC0 : 0<C0 := by
    have hn := Finset.sum_nonneg (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>(hC A).le)
    dsimp only [C0]
    linarith
  refine ⟨C0,hC0,?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with Z hZ
  have hz1 : 1<Z := (hZ ∅).1
  have hz : 0<Z := lt_trans zero_lt_one hz1
  refine ⟨hz1,?_⟩
  intro T hT hout hdis hnorm
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  rw [hidentity η (calibrationForSet S hS) W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    _ hslots (fun i=>Z^(ell i)) (fun i=>by positivity)
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hz]
  apply (norm_sum_le _ _).trans
  have hterm (A : Finset (Fin K)) :
      ‖∑'j : ℕ,lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i)) W
        (fun i=>Z^(ell i)) A (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) ((2:ℝ)^j)
        (Z*∏i∈Finset.univ\A,Z^(ell i)) (V A) (hV A)‖≤C A*Z^(3/16+256*ε) := by
    have hc : Z*(∏i∈Finset.univ\A,Z^(ell i))=Z^(1+lowSelectedLength ell A) := by
      rw [lowSelectedScale_product ell A Z hz,Real.rpow_add hz,Real.rpow_one]
    rw [hc]
    exact ((hZ A).2 T hT hout hdis hnorm A W hWnorm).2
  have hh := Finset.sum_le_sum (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>hterm A)
  apply hh.trans
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C0];linarith) (Real.rpow_nonneg hz.le _)

theorem original_ray_compensatedPhysicalProbe_low (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6) (R : Set Id)
    (a b ε : ℝ) (ha : 0<a) (hab : a≤b) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤C*Z^(3/16+256*ε) := by
  obtain ⟨C,hC,he⟩ := compensatedPhysicalProbe_low η S hmax hS.bad ell hell hsum
    a b ε ha hε hε1 W hW hWnorm W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨C,hC,?_⟩
  filter_upwards [he,ProbeRaySlots.power_pools_eventually_disjoint R S (fun _=>a) (fun _=>b) ell
    (fun _=>ha) (fun _=>hab) hinj] with Z hZ hd
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  apply hZ.2 _ (fun i=>ProbeRaySlots.pool_supported R S hS a b (Z^(ell i)))
    (fun i P hP=>((ProbeRaySlots.mem_pool R S a b (Z^(ell i)) P).mp hP).2.2.2)
    (fun i j hij=>hd i j hij)
  intro i P hP
  have hh := ProbeRaySlots.pool_norm_bounds R S ha.le hab (Real.rpow_pos_of_pos hz _) P hP
  simpa only [mul_comm] using And.intro hh.1.le hh.2

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowWindowBound
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma compensatedPhysicalProbe_window_scale {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) (c : ℂ) :
    compensatedPhysicalProbe η C W0 W1 slots (fun i x=>c*W i x) Yp X Y Z=
      c^K*compensatedPhysicalProbe η C W0 W1 slots W Yp X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_assoc]
  exact (Finset.mul_sum ..).symm

theorem original_ray_compensatedPhysicalProbe_low_loss_oai
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6) (R : Set Id)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤C*Z^(3/16+loss) := by
  let D := max 1 B
  have hD : 0<D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDc : (D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hD.ne'
  let Wn := fun i x=>W i x/(D:ℂ)
  have hWn : ∀i,Function.support (Wn i)⊆Set.Icc a b := by
    intro i x hx
    apply hW i
    intro hz
    exact hx (by dsimp [Wn];rw [hz,zero_div])
  have hn : ∀i x,‖Wn i x‖≤1 := by
    intro i x
    dsimp only [Wn]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
    exact (div_le_one hD).mpr ((hWnorm i x).trans (le_max_right _ _))
  have hscale : (fun i x=>(D:ℂ)*Wn i x)=W := by
    funext i x
    dsimp [Wn]
    field_simp
  let ε := min (loss/512) (1/2)
  have he : 0<ε := by dsimp [ε];positivity
  have he1 : ε<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heloss : 256*ε≤loss := by have hh := min_le_left (loss/512) (1/2:ℝ);dsimp only [ε];linarith
  intro η
  obtain ⟨C,hC,hbound⟩ := original_ray_compensatedPhysicalProbe_low η S hS hmax ell hell hinj hsum R
    a b ε ha hab he he1 Wn hWn hn W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨D^K*C,by positivity,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  have heq := compensatedPhysicalProbe_window_scale η (calibrationForSet S hmax) W0 W1
    (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) Wn (fun i=>Z^(ell i))
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (D:ℂ)
  rw [hscale] at heq
  rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
  calc
    _≤D^K*(C*Z^(3/16+256*ε)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _≤D^K*(C*Z^(3/16+loss)) := by gcongr
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_loss_oai := @OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_loss_oai
