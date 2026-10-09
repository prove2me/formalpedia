-- Prove2me | solution 1 for OAI.SevenEighths.HeckePrimeAmplitudeActual.ray_amplitude_bins
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:18:07.548083+00:00
-- url     : https://prove2.me/submissions/cc23f50a-172b-430f-bca4-96e25df3d63d

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017
import Theorems.Thm_OAI_SevenEighths_HeckePrimeDyadic_scaled_direct_bound
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
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

open scoped BigOperators Classical

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem mellinLogFamily_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hv : V (Real.exp (-u)) ≠ 0 := by
    intro hv
    exact hu (by simp [mellinLogFamily, hv])
  have hm := hsupp hv
  have hlow := Real.log_le_log ha hm.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hm.2
  simp only [Real.log_exp] at hlow hhigh
  constructor <;> linarith

theorem mellin_eq_logFamily_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * Complex.I) = 𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero,  sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, Complex.I_im, mul_one, zero_add]
  rfl

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

theorem columnDyadicLength_small_power (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N) :
    (columnDyadicLength N + 1 : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  have hL : (columnDyadicLength N + 1 : ℝ) ≤ 2 + Real.log N / Real.log 2 := by
    dsimp only [columnDyadicLength]
    linarith
  have hr : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hb : Real.log N / Real.log 2 ≤ (N ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hε) hlog.le
  calc
    _ ≤ 2 + Real.log N / Real.log 2 := hL
    _ ≤ 2 * N ^ ε + (N ^ ε / ε) / Real.log 2 := add_le_add (by linarith) hb
    _ = _ := by field_simp

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SmoothSummands
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
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ)^(divisorDyadicLabel N D).val/2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^(divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dif_pos ⟨hD,hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

theorem sum_divisorDyadicBins {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (N : ℝ) (f : Ideal O → A) :
    (∑ D ∈ S, f D) = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j, f D := by
  simp only [divisorDyadicBin,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  simp

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.TransformedColumns
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

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

theorem finite_inverse_norm_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤256*(columnDyadicLength H+1:ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑I∈divisorDyadicBin S H j,1/(Ideal.absNorm I:ℝ))≤256 := by
    have hp : 0<(2:ℝ)^j.val := by positivity
    have hone : 1≤(2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card:ℝ)≤128*(2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I∈divisorDyadicBin S H j) :
        1/(Ideal.absNorm I:ℝ)≤2/(2:ℝ)^j.val := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      apply (div_le_div_iff₀ (by linarith [hpos I hIS]) hp).mpr
      linarith
    calc
      _ ≤ ∑_I∈divisorDyadicBin S H j,2/(2:ℝ)^j.val := Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card:ℝ)*(2/(2:ℝ)^j.val) := by simp
      _ ≤ (128*(2:ℝ)^j.val)*(2/(2:ℝ)^j.val) := by gcongr
      _ = _ := by field_simp; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑j : Fin (columnDyadicLength H+1),(256:ℝ) := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp; ring

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CubeBlocks
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

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid

theorem powerfulBase_spec (I : Ideal O) (hI : PowerfulIdeal I) :
    powerfulBase I≠0 ∧ powerfulBase I ^2*squarefreePart I ^3=I := by
  rw [powerfulBase,dif_pos hI]
  exact (powerful_exists_square_cube I hI).choose_spec

theorem powerfulBase_injective_on_fiber (I J : Ideal O)
    (hI : PowerfulIdeal I) (hJ : PowerfulIdeal J)
    (hb : squarefreePart I=squarefreePart J) (ha : powerfulBase I=powerfulBase J) : I=J := by
  rw [←(powerfulBase_spec I hI).2,←(powerfulBase_spec J hJ).2,ha,hb]

theorem powerfulBase_norm_bound (I : Ideal O) (hI : PowerfulIdeal I) (X : ℝ)
    (hX : (Ideal.absNorm I:ℝ)≤X) :
    1≤(Ideal.absNorm (squarefreePart I):ℝ) ∧
    (Ideal.absNorm (squarefreePart I):ℝ)≤X ∧
    (Ideal.absNorm (powerfulBase I):ℝ)≤Real.sqrt X/(Ideal.absNorm (squarefreePart I):ℝ) := by
  have ha := (powerfulBase_spec I hI).1
  have hb := (squarefree_squarefreePart I).ne_zero
  have ha1 : 1≤(Ideal.absNorm (powerfulBase I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => ha (Ideal.absNorm_eq_zero_iff.mp hz))
  have hb1 : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hb (Ideal.absNorm_eq_zero_iff.mp hz))
  have hnorm : (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3=(Ideal.absNorm I:ℝ) := by
    have h := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (powerfulBase_spec I hI).2
    simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using h
  have hX0 : 0≤X := (Nat.cast_nonneg _).trans hX
  have hb2 : (Ideal.absNorm (squarefreePart I):ℝ)≤(Ideal.absNorm (squarefreePart I):ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show (1:ℕ)≤3 by decide)
  have hab : ((Ideal.absNorm (powerfulBase I):ℝ)*(Ideal.absNorm (squarefreePart I):ℝ))^2≤X := by
    calc
      _ = (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^2 := by ring
      _ ≤ (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by decide)) (sq_nonneg _)
      _ ≤ X := hnorm.trans_le hX
  have hbX : (Ideal.absNorm (squarefreePart I):ℝ)≤X := by
    calc
      _ ≤ (Ideal.absNorm (squarefreePart I):ℝ)^3 := hb2
      _ ≤ (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3 :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ ha1)
      _ ≤ X := hnorm.trans_le hX
  refine ⟨hb1,hbX,?_⟩
  apply (le_div_iff₀ (by linarith : 0<(Ideal.absNorm (squarefreePart I):ℝ))).mpr
  nlinarith [Real.sq_sqrt hX0,Real.sqrt_nonneg X]

end

open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel

theorem powerful_fiber_count (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X)
    (B : Ideal O) (hB : B∈S.image squarefreePart) :
    ((S.filter (fun I => squarefreePart I=B)).card:ℝ)≤128*Real.sqrt X/(Ideal.absNorm B:ℝ) := by
  obtain ⟨I,hI,hIB⟩ := Finset.mem_image.mp hB
  have hi := hS I hI
  have hnorm := powerfulBase_norm_bound I hi.1 X hi.2
  rw [hIB] at hnorm
  have hAb : 1≤(Ideal.absNorm (powerfulBase I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => (powerfulBase_spec I hi.1).1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤Real.sqrt X/(Ideal.absNorm B:ℝ) := hAb.trans hnorm.2.2
  let T := S.filter (fun I => squarefreePart I=B)
  have hinj : Set.InjOn powerfulBase T := by
    intro J hJ lengthScale hL he
    exact powerfulBase_injective_on_fiber J lengthScale (hS J (Finset.mem_filter.mp hJ).1).1
      (hS lengthScale (Finset.mem_filter.mp hL).1).1
      ((Finset.mem_filter.mp hJ).2.trans (Finset.mem_filter.mp hL).2.symm) he
  have hcard : (T.image powerfulBase).card=T.card := Finset.card_image_iff.mpr hinj
  have hcount := DescentFiberCost.finite_ideal_count_real (T.image powerfulBase)
    (Real.sqrt X/(Ideal.absNorm B:ℝ)) hscale (fun J hJ => by
      obtain ⟨lengthScale,hL,rfl⟩ := Finset.mem_image.mp hJ
      exact (powerfulBase_spec lengthScale (hS lengthScale (Finset.mem_filter.mp hL).1).1).1) (fun J hJ => by
      obtain ⟨lengthScale,hL,rfl⟩ := Finset.mem_image.mp hJ
      have hp := powerfulBase_norm_bound lengthScale (hS lengthScale (Finset.mem_filter.mp hL).1).1 X
        (hS lengthScale (Finset.mem_filter.mp hL).1).2
      simpa only [(Finset.mem_filter.mp hL).2] using hp.2.2)
  rw [hcard] at hcount
  simpa only [mul_div_assoc] using hcount

theorem powerful_ideal_count_log (S : Finset (Ideal O)) (X : ℝ) (hX : 1≤X)
    (hS : ∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X) :
    (S.card:ℝ)≤32768*Real.sqrt X*(columnDyadicLength X+1:ℝ) := by
  let B := S.image squarefreePart
  have hBn (J : Ideal O) (hJ : J∈B) : J≠0 ∧ (Ideal.absNorm J:ℝ)≤X := by
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact ⟨(squarefree_squarefreePart I).ne_zero,(powerfulBase_norm_bound I (hS I hI).1 X (hS I hI).2).2.1⟩
  have he : (S.card:ℝ)=∑J∈B,((S.filter (fun I => squarefreePart I=J)).card:ℝ) := by
    calc
      _ = ∑_I∈S,(1:ℝ) := by simp
      _ = ∑J∈B,∑_I∈S.filter (fun I => squarefreePart I=J),(1:ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem squarefreePart hI) _).symm
      _ = _ := by simp
  rw [he]
  calc
    _ ≤ ∑J∈B,128*Real.sqrt X/(Ideal.absNorm J:ℝ) := Finset.sum_le_sum (fun J hJ => powerful_fiber_count S X hS J hJ)
    _ = (128*Real.sqrt X)*∑J∈B,1/(Ideal.absNorm J:ℝ) := by rw [Finset.mul_sum]; congr 1; ext J; ring
    _ ≤ (128*Real.sqrt X)*(256*(columnDyadicLength X+1:ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_inverse_norm_sum B X (fun J hJ => (hBn J hJ).1)
        (fun J hJ => (hBn J hJ).2)) (by positivity)
    _ = _ := by ring

theorem powerful_ideal_count (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (X : ℝ), 1≤X →
      (∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X) →
      (S.card:ℝ)≤C*X^(1/2+ε) := by
  let C := 32768*(2+1/(ε*Real.log 2))
  have hC : 0<C := by have hl : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro S X hX hS
  apply (powerful_ideal_count_log S X hX hS).trans
  calc
    _ ≤ 32768*Real.sqrt X*((2+1/(ε*Real.log 2))*X^ε) :=
      mul_le_mul_of_nonneg_left (columnDyadicLength_small_power ε hε X hX) (by positivity)
    _ = C*X^(1/2+ε) := by
      rw [Real.rpow_add (by linarith : 0<X),←Real.sqrt_eq_rpow]
      dsimp [C]
      ring

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CompactProfileFamily
namespace OAI

noncomputable section
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.CompactProfileFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem section_deriv_smooth (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : E × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : E × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : E × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : E) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end SevenEighths.CompactProfileFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicTailBudget
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem exists_external_tail_order (τ B p : ℝ) (hτ : 0<τ) :
    ∃ n : ℕ, ∀ Z : ℝ, 1≤Z → Z^B/(1+Z^τ)^n≤Z^p := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((B-p)/τ)
  refine ⟨n,?_⟩
  intro Z hZ
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hn' : B≤p+τ*(n : ℝ) := by
    have h := (div_lt_iff₀ hτ).mp hn
    nlinarith
  have hden : 0<(1+Z^τ)^n := by positivity
  apply (div_le_iff₀ hden).mpr
  calc
    Z^B ≤ Z^(p+τ*(n : ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hn'
    _ = Z^p*(Z^τ)^n := by
      rw [Real.rpow_add hZp,Real.rpow_mul hZp.le,Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hZp.le _) (by linarith) n)
      (Real.rpow_nonneg hZp.le _)

theorem constant_absorbed_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, C≤Z^ε := by
  exact (tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop C)

theorem uniform_external_tail_order (τ dmax B R : ℝ)
    (hτ : 0<τ) (_hdmax : 0≤dmax) (hB : 0≤B) (hR : 0≤R) :
    ∃ n : ℕ, ∀ Z d p : ℝ, 1≤Z → 0≤d → d≤dmax → -R≤p →
      (Z^d)^B/(1+Z^τ/2)^n≤(2 : ℝ)^n*(Z^d)^p := by
  obtain ⟨n,hn⟩ := exists_external_tail_order τ (dmax*B) (-dmax*R) hτ
  refine ⟨n,?_⟩
  intro Z d p hZ hd hd' hp
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hnum : (Z^d)^B≤Z^(dmax*B) := by
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd' hB)
  have htarget : Z^(-dmax*R)≤(Z^d)^p := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    nlinarith [mul_nonneg hd (show 0≤p+R by linarith),
      mul_nonneg (show 0≤dmax-d by linarith) hR]
  have hden : ((1+Z^τ)/2)^n≤(1+Z^τ/2)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ (Z^(dmax*B))/((1+Z^τ)/2)^n :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (2 : ℝ)^n*(Z^(dmax*B)/(1+Z^τ)^n) := by
      rw [div_pow]
      field_simp
    _ ≤ (2 : ℝ)^n*Z^(-dmax*R) := mul_le_mul_of_nonneg_left (hn Z hZ) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left htarget (by positivity)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealMangoldt
namespace OAI

namespace SevenEighths.IdealMangoldt

open ActualEisensteinCubic UniqueFactorizationMonoid ArithmeticFunction
open scoped BigOperators Classical

noncomputable section

theorem primeBase_spec {I : Ideal O} (hI : IsPrimePow I) :
    Prime (primeBase I) ∧ ∃ k : ℕ, 0 < k ∧ primeBase I ^ k = I := by
  obtain ⟨k, hp, hk, heq⟩ := hI.choose_spec
  simp only [primeBase, hI, dite_true]
  exact ⟨hp, k, hk, heq⟩

theorem primeBase_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    primeBase (P ^ k) = P := by
  have hpow : IsPrimePow (P ^ k) := ⟨P, k, hP, hk, rfl⟩
  obtain ⟨hQ, l, hl, heq⟩ := primeBase_spec hpow
  apply associated_iff_eq.mp
  apply hQ.associated_of_dvd hP
  exact hQ.dvd_of_dvd_pow (heq ▸ dvd_pow_self (primeBase (P ^ k)) hl.ne')

theorem value_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    value (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [value, if_pos (show IsPrimePow (P ^ k) from ⟨P, k, hP, hk, rfl⟩),
    primeBase_pow hP hk]

theorem value_nonneg (I : Ideal O) : 0 ≤ value I := by
  by_cases hI : IsPrimePow I
  · rw [value, if_pos hI]
    apply Real.log_nonneg
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨_, (primeBase_spec hI).1⟩).trans' (by decide : 1 ≤ 2)
  · simp only [value, hI, ite_false, le_refl]

end

end SevenEighths.IdealMangoldt

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealLogDerivative
namespace OAI

namespace SevenEighths.IdealLogDerivative

open ActualEisensteinCubic UniqueFactorizationMonoid IdealEuler
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical Topology

noncomputable section

theorem value_le_log_norm (B : Ideal O) :
    IdealMangoldt.value B ≤ Real.log (Ideal.absNorm B) := by
  by_cases h : IsPrimePow B
  · obtain ⟨P, k, hP, hk, rfl⟩ := h
    rw [IdealMangoldt.value_pow hP hk, map_pow, Nat.cast_pow, Real.log_pow]
    apply le_mul_of_one_le_left
    · exact Real.log_natCast_nonneg _
    · exact_mod_cast hk
  · rw [IdealMangoldt.value, if_neg h]
    exact Real.log_natCast_nonneg _

end
end SevenEighths.IdealLogDerivative

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeCounting.IdealPrimeMass
namespace OAI

namespace SevenEighths.PNT.IdealPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter
open SevenEighths.IdealMangoldt
open scoped BigOperators Classical Topology

noncomputable section

theorem value_prime {P : Ideal O} (hP : Prime P) : value P = Real.log (Ideal.absNorm P) := by
  simpa only [pow_one] using value_pow hP (k := 1) (by decide)

end

end SevenEighths.PNT.IdealPrimeMass

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimePowers
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckePrimePowers
open HeckeFamily UniqueFactorizationMonoid

theorem nonprime_primePow_powerful {I : Ideal O} (hpow : IsPrimePow I) (hprime : ¬Prime I) :
    CompletedGauss.PowerfulIdeal I := by
  obtain ⟨P,k,hP,hk,rfl⟩ := hpow
  have hk2 : 2≤k := by
    by_contra h
    have hk1 : k=1 := by omega
    subst k
    exact hprime (by simpa using hP)
  refine ⟨pow_ne_zero _ hP.ne_zero,?_⟩
  intro Q hQ
  rw [hP.irreducible.normalizedFactors_pow] at hQ ⊢
  have hQP := (Multiset.mem_replicate.mp hQ).2
  subst Q
  simpa using hk2

theorem logWeight_nonneg (I : Ideal O) : 0≤logWeight I :=
  div_nonneg (IdealMangoldt.value_nonneg _) (Real.log_natCast_nonneg _)

theorem logWeight_le_one (I : Ideal O) : logWeight I≤1 := by
  by_cases hlog : Real.log (Ideal.absNorm I)=0
  · simp [logWeight,hlog]
  · apply (div_le_one (lt_of_le_of_ne (Real.log_natCast_nonneg _) (Ne.symm hlog))).mpr
    exact IdealLogDerivative.value_le_log_norm I

theorem logWeight_prime {P : Ideal O} (hP : Prime P) : logWeight P=1 := by
  have hp2 : (2 : ℝ)≤P.absNorm := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
  have hp : 0<Real.log (P.absNorm : ℝ) := Real.log_pos (by linarith)
  rw [logWeight, PNT.IdealPrimeMass.value_prime hP, div_self hp.ne']

theorem logWeight_eq_zero {I : Ideal O} (hI : ¬IsPrimePow I) : logWeight I=0 := by
  simp only [logWeight, IdealMangoldt.value, if_neg hI, zero_div]

theorem sum_prime_extraction (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
      (∑ I∈S.filter Prime, idealCoeff χ I*f I) =
      ∑ I∈S.filter (fun I => IsPrimePow I ∧ ¬Prime I),
        (logWeight I : ℂ)*idealCoeff χ I*f I := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hP : Prime I
  · simp only [hP, ite_true, not_true_eq_false, and_false, ite_false,
      logWeight_prime hP, Complex.ofReal_one, one_mul, sub_self]
  · by_cases hp : IsPrimePow I
    · simp [hP,hp]
    · simp [hP,hp,logWeight_eq_zero hp]

theorem prime_extraction_error (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ)
      (X B : ℝ), 1≤X → 0≤B →
      (∀ I∈S, (I.absNorm : ℝ)≤X) → (∀ I∈S, ‖f I‖≤B) →
      ‖(∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
        (∑ I∈S.filter Prime, idealCoeff χ I*f I)‖ ≤ C*X^(1/2+ε)*B := by
  obtain ⟨C,hC,hcount⟩ := CompletedGauss.powerful_ideal_count ε hε
  refine ⟨C,hC,?_⟩
  intro χ S f X B hX hB hnorm hf
  rw [sum_prime_extraction]
  let A := S.filter (fun I => IsPrimePow I ∧ ¬Prime I)
  have hA : (A.card : ℝ)≤C*X^(1/2+ε) := by
    apply hcount A X hX
    intro I hI
    obtain ⟨hIS,hpow,hprime⟩ := Finset.mem_filter.mp hI
    exact ⟨nonprime_primePow_powerful hpow hprime,hnorm I hIS⟩
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _I∈A, B := by
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (logWeight_nonneg _)]
      have hcoeff : logWeight I*‖idealCoeff χ I‖≤1 :=
        (mul_le_of_le_one_right (logWeight_nonneg I) (idealCoeff_norm_le_one χ I)).trans
          (logWeight_le_one I)
      exact (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans
        (by simpa using hf I (Finset.mem_filter.mp hI).1)
    _ = (A.card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hA hB

end SevenEighths.HeckePrimePowers

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeLogProfile
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace SevenEighths.PrimeLogProfile

theorem safeInverse_eq (x : ℝ) (hx : 1/2≤|x|) : safeInverse x=(x : ℂ)⁻¹ := by
  have hz : QuadraticInitialBound.sieveBump (4*x)=0 := by
    apply QuadraticInitialBound.sieveBump.zero_of_le_dist
    change 2≤dist (4*x) 0
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
    norm_num
    linarith
  simp [safeInverse, QuadraticInitialBound.sieveCutoff_apply, hz]

theorem safeInverse_smooth : ContDiff ℝ ∞ safeInverse := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : safeInverse =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ)<1/4)] with y hy
      have hy' : |y|<1/4 := by simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hy
      have hone : QuadraticInitialBound.sieveBump (4*y)=1 := by
        apply QuadraticInitialBound.sieveBump.one_of_mem_closedBall
        change dist (4*y) 0≤1
        rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
        norm_num
        linarith
      simp [safeInverse, QuadraticInitialBound.sieveCutoff_apply, hone]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hnum : ContDiff ℝ ∞ (fun y : ℝ => (1 : ℂ)-QuadraticInitialBound.sieveCutoff (4*y)) :=
      contDiff_const.sub ((QuadraticInitialBound.sieveCutoff.smooth ⊤).comp
        (contDiff_const.mul contDiff_id))
    change ContDiffAt ℝ ∞ (fun y : ℝ => (1-QuadraticInitialBound.sieveCutoff (4*y))/(y : ℂ)) x
    simpa only [div_eq_mul_inv, Pi.inv_apply, Complex.ofRealCLM_apply] using hnum.contDiffAt.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr hx))

theorem profile_support (W : ℝ→ℂ) (A : ℝ) :
    Function.support (profile W A) ⊆ Function.support W := by
  intro y hy hW
  exact hy (by simp [profile,hW])

theorem profile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (A : ℝ) :
    ContDiff ℝ ∞ (profile W A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y=0
  · subst y
    have he : profile W A =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [(isOpen_Iio.mem_nhds ha)] with y hy
      have hw : W y=0 := by
        by_contra hh
        exact (not_le_of_gt hy) (hWs hh).1
      simp [profile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact ((hW.contDiffAt.mul contDiffAt_const).mul
      (safeInverse_smooth.contDiffAt.comp y
        (contDiffAt_const.add (contDiffAt_const.mul (Real.contDiffAt_log.mpr hy)))))

theorem logFamily_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (logFamily W)) := by
  change ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ =>
    Real.exp (-p.1.2*p.2) • (W (Real.exp (-p.2)) * (p.1.1 : ℂ) * safeInverse (1-p.1.1*p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.snd.neg.mul contDiff_snd)).smul
    (((hW.comp (Real.contDiff_exp.comp contDiff_snd.neg)).mul
      (Complex.ofRealCLM.contDiff.comp contDiff_fst.fst)).mul
      (safeInverse_smooth.comp (contDiff_const.sub (contDiff_fst.fst.mul contDiff_snd))))

theorem logFamily_eq (W : ℝ→ℂ) (A σ u : ℝ) :
    logFamily W (A,σ) u = CubicReflectionKernel.mellinLogFamily (profile W A) σ u := by
  simp only [logFamily, CubicReflectionKernel.mellinLogFamily, profile, Real.log_exp]
  congr 3
  ring

theorem logFamily_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (logFamily W p) ⊆ Icc (-Real.log b) (-Real.log a) := by
  have he : logFamily W p = CubicReflectionKernel.mellinLogFamily (profile W p.1) p.2 := by
    funext u
    exact logFamily_eq W p.1 p.2 u
  rw [he]
  exact CubicReflectionKernel.mellinLogFamily_support _ a b ha ((profile_support W p.1).trans hWs) _

theorem uniform_mellin_decay (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ A ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (profile W A) ((σ : ℂ)+t*Complex.I)‖≤C := by
  obtain ⟨C,hC,hb⟩ := CompactProfileFamily.compact_family_fourier_weighted_bound
    (logFamily W) (logFamily_smooth W hW)
    (Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (logFamily_support W a b ha hWs)
    ((Icc (0 : ℝ) 1) ×ˢ (Icc lo hi)) (isCompact_Icc.prod isCompact_Icc) j
  refine ⟨(1+2*Real.pi)^j*C,by positivity,?_⟩
  intro A hA σ hσ t
  rw [CubicReflectionKernel.mellin_eq_logFamily_fourier]
  have he : CubicReflectionKernel.mellinLogFamily (profile W A) σ = logFamily W (A,σ) := by
    funext u
    exact (logFamily_eq W A σ u).symm
  rw [he]
  have ht : |t|=(2*Real.pi)*|t/(2*Real.pi)| := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  have hbase : 1+|t|≤(1+2*Real.pi)*(1+|t/(2*Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos,abs_nonneg (t/(2*Real.pi))]
  calc
    _ ≤ ((1+2*Real.pi)*(1+|t/(2*Real.pi)|))^j *
        ‖𝓕 (logFamily W (A,σ)) (t/(2*Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1+2*Real.pi)^j*((1+|t/(2*Real.pi)|)^j *
        ‖𝓕 (logFamily W (A,σ)) (t/(2*Real.pi))‖) := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (A,σ) ⟨hA,hσ⟩ _) (by positivity)

theorem profile_eq_log_division (W : ℝ→ℂ) (a b P : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hP : 0<P)
    (hlarge : 2*(|Real.log a|+|Real.log b|)+1≤Real.log P) :
    profile W (1/Real.log P) = fun y => W y / (Real.log (P*y) : ℂ) := by
  funext y
  by_cases hy : W y=0
  · simp [profile,hy]
  have hs := hWs hy
  have hyp : 0<y := ha.trans_le hs.1
  have hlogs : |Real.log y|≤|Real.log a|+|Real.log b| := by
    apply abs_le.mpr
    constructor
    · have h := Real.log_le_log ha hs.1
      linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
    · have h := Real.log_le_log hyp hs.2
      linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]
  have hp : 0<Real.log P := by linarith [abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
  have hhalf : 1/2≤1+(1/Real.log P)*Real.log y := by
    have he : 1+(1/Real.log P)*Real.log y = (Real.log P+Real.log y)/Real.log P := by field_simp
    rw [he]
    apply (le_div_iff₀ hp).mpr
    linarith [(abs_le.mp hlogs).1]
  have hi := safeInverse_eq (1+(1/Real.log P)*Real.log y)
    (hhalf.trans (le_abs_self _))
  rw [profile,hi,Real.log_mul (ne_of_gt hP) (ne_of_gt hyp)]
  push_cast
  have hn : (Real.log P : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hn' : (Real.log P : ℂ)+(Real.log y : ℂ)≠0 := by
    have : 0<Real.log P+Real.log y := by
      linarith [(abs_le.mp hlogs).1,abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
    exact_mod_cast this.ne'
  field_simp

end SevenEighths.PrimeLogProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Set
namespace SevenEighths.HeckePrimeAnnular
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem annular_support (W : ℝ→ℂ) (a b D : ℝ) (ha : 0<a) (hD : 0<D)
    (hWs : Function.support W⊆Icc a b) (I : Ideal O)
    (hw : W ((I.absNorm : ℝ)/D)≠0) : I∈annulusSet b D := by
  have hs := hWs hw
  apply mem_idealsUpTo.mpr
  constructor
  · have hnorm : 0<(I.absNorm : ℝ) := by
      have := (le_div_iff₀ hD).mp hs.1
      nlinarith
    exact_mod_cast hnorm
  · have hn := (div_le_iff₀ hD).mp hs.2
    exact Nat.le_floor (hn.trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))

theorem log_polynomial_eq_finite (χ : Character) (W : ℝ→ℂ) (a b D σ freq : ℝ)
    (ha : 0<a) (hD : 0<D) (hWs : Function.support W⊆Icc a b)
    (hlarge : 2*(|Real.log a|+|Real.log b|)+1≤Real.log D) :
    HeckePrimeDyadic.polynomial χ (PrimeLogProfile.profile W (1/Real.log D)) D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ I∈annulusSet b D,
        (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I := by
  rw [PrimeLogProfile.profile_eq_log_division W a b D ha hWs hD hlarge]
  unfold HeckePrimeDyadic.polynomial
  congr 1
  have he : (fun I : NonzeroIdeal => HeckePrimeDyadic.summand χ
      (fun y => W y/(Real.log (D*y) : ℂ)) D σ freq I) =
      fun I : NonzeroIdeal => (HeckePrimePowers.logWeight I.val : ℂ)*
        idealCoeff χ I.val*annularWeight W D σ freq I.val := by
    funext I
    unfold HeckePrimeDyadic.summand HeckePrimeDyadic.coefficient annularWeight
    dsimp only [HeckePrimePowers.logWeight, HeckeDyadic.norm]
    rw [mul_div_cancel₀ _ hD.ne']
    simp only [Complex.ofReal_div]
    ring
  rw [he]
  calc
    _ = ∑' I : Ideal O, (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I := by
      apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I≠0})
        (f := fun I : Ideal O => (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I)
      intro I hI hzero
      subst I
      exact hI (by simp [HeckePrimePowers.logWeight])
    _ = _ := by
      apply tsum_eq_sum
      intro I hI
      have hw : W ((I.absNorm : ℝ)/D)=0 := by
        by_contra hh
        exact hI (annular_support W a b D ha hD hWs I hh)
      simp [annularWeight,hw]

theorem extraction_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character) (W : ℝ→ℂ) (a b D σ freq B : ℝ),
      0<a → 1≤D → Function.support W⊆Icc a b →
      2*(|Real.log a|+|Real.log b|)+1≤Real.log D → 0≤B →
      (∀ y∈Icc a b, ‖W y‖*y^(-σ)≤B) →
      ‖HeckePrimeDyadic.polynomial χ (PrimeLogProfile.profile W (1/Real.log D)) D σ freq -
        primePolynomial χ W b D σ freq‖≤
        C*(max 1 b)^((1/2 : ℝ)+ε)*D^ε*B := by
  obtain ⟨C,hC,herr⟩ := HeckePrimePowers.prime_extraction_error ε hε
  refine ⟨C,hC,?_⟩
  intro χ W a b D σ freq B ha hD hWs hlarge hB hWbound
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hX : 1≤ max 1 b*D := hD.trans (le_mul_of_one_le_left hDp.le (le_max_left _ _))
  have hnorm (I : Ideal O) (hI : I∈annulusSet b D) : (I.absNorm : ℝ)≤ max 1 b*D := by
    exact (Nat.cast_le.mpr (mem_idealsUpTo.mp hI).2).trans
      (Nat.floor_le (by positivity))
  have hw (I : Ideal O) (_hI : I∈annulusSet b D) : ‖annularWeight W D σ freq I‖≤B := by
    by_cases hz : W ((I.absNorm : ℝ)/D)=0
    · simpa [annularWeight,hz] using hB
    · have hs := hWs hz
      have hy : 0<(I.absNorm : ℝ)/D := ha.trans_le hs.1
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simpa only [Complex.neg_re,shift_re] using hWbound _ hs
  have hb := herr χ (annulusSet b D) (annularWeight W D σ freq) (max 1 b*D) B
    hX hB hnorm hw
  have hn : ‖(D : ℂ)^(-(1/2 : ℂ))‖=D^(-(1/2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hDp]
    norm_num
  rw [log_polynomial_eq_finite χ W a b D σ freq ha hDp hWs hlarge,
    primePolynomial,←mul_sub,norm_mul,hn]
  calc
    _ ≤ D^(-(1/2 : ℝ))*(C*(max 1 b*D)^(1/2+ε)*B) := by
      exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hDp.le _)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤ max 1 b) hDp.le]
      have he : D^(-(1/2 : ℝ))*D^(1/2+ε)=D^ε := by
        rw [←Real.rpow_add hDp]
        congr 1
        ring
      calc
        _ = C*(max 1 b)^(1/2+ε)*(D^(-(1/2 : ℝ))*D^(1/2+ε))*B := by ring
        _ = _ := by rw [he]

end SevenEighths.HeckePrimeAnnular

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicSource
namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem source_log_profile_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq L : ℝ,
      0≤ r → r≤R → σmin≤σ → σ≤σmax → L∈Icc (0 : ℝ) 1 →
      ∀ k : ι, (χ k).modulus.absNorm≤Z^d →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖polynomial (χ k) (PrimeLogProfile.profile W L) ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨Cd,hCd,hdirect⟩ := scaled_direct_bound e κ η he he' hκ hη
  obtain ⟨n,htail⟩ := uniform_external_tail_order τ dmax (2*R+κ) 0
    hτ hdmax (by positivity) (by norm_num)
  obtain ⟨C₂,hC₂,hm₂⟩ := PrimeLogProfile.uniform_mellin_decay W A B hA hWs hW
    (-σmax) (2-σmin) 2
  obtain ⟨Cn,hCn,hmn⟩ := PrimeLogProfile.uniform_mellin_decay W A B hA hWs hW
    (-σmax) (2-σmin) (n+2)
  refine ⟨Cd*C₂+Cd*Cn*(2 : ℝ)^n,by positivity,?_⟩
  intro Z d hZ hd hd' hU2 hT ι _ χ hχ a i ha ha' hmax r σ freq L
    hr hrR hσmin hσmax hL k hQ hfreq hheight
  let U := Z^d
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hs : Icc (a+8*e-σ) (2-σ)⊆Icc (-σmax) (2-σmin) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hleft : a+8*e-σ∈Icc (-σmax) (2-σmin) := by
    constructor <;> linarith
  have hb := hdirect χ hχ (Z^τ) a i hT ha ha' hmax k
    (PrimeLogProfile.profile W L) A B hA
    ((PrimeLogProfile.profile_support W L).trans hWs)
    (PrimeLogProfile.profile_smooth W A B hA hWs hW L)
    U r R σ freq (Z^τ/2) C₂ Cn n hU2 hQ hr hrR (by positivity)
    hfreq hheight hC₂.le hCn.le (hm₂ L hL _ hleft) (fun x hx => hmn L hL x (hs hx))
  have htail' := htail Z d 0 hZ hd hd' (by norm_num)
  simp only [Real.rpow_zero,mul_one] at htail'
  have hexp : (a-1/2+8*e)*r+κ≤(a-1/2)*r+ε := by
    nlinarith [mul_le_mul_of_nonneg_left hrR (by positivity : 0≤8*e)]
  have hp : 0≤(a-1/2)*r+ε := by
    have : 0≤8*e*R := by positivity
    nlinarith [mul_nonneg (show 0≤a-1/2 by linarith) hr]
  calc
    _ ≤ Cd*C₂*U^((a-1/2)*r+ε)+Cd*Cn*(2 : ℝ)^n := by
      apply hb.trans
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hexp) (by positivity)
      · calc
          _ = (Cd*Cn)*(U^(2*R+κ)/(1+Z^τ/2)^n) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left htail' (by positivity)
    _ ≤ (Cd*C₂+Cd*Cn*(2 : ℝ)^n)*U^((a-1/2)*r+ε) := by
      rw [add_mul]
      apply add_le_add (le_refl _)
      exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hU hp)

end SevenEighths.HeckePrimeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeBin
namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeAnnular
open HeckeFamily HeckeDyadic

theorem prime_bin_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, 0≤ r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      ∀ k : ι, (χ k).modulus.absNorm≤Z^d →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖primePolynomial (χ k) W B ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨Cp,hCp,hprime⟩ := HeckePrimeDyadic.source_log_profile_bound W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ he he' hκ hη hbudget
  let ξ := ε/(R+1)
  have hξ : 0<ξ := div_pos hε (by positivity)
  obtain ⟨Ce,hCe,herror⟩ := extraction_bound ξ hξ
  obtain ⟨Bf,hBf,hprofile⟩ := fixed_profile_norm_bound W hW.continuous A B σmin σmax hA
  let E := Ce*(max 1 B)^(1/2+ξ)*Bf
  have hE : 0<E := by dsimp [E]; positivity
  refine ⟨Cp+E,by positivity,?_⟩
  intro Z d hZ hd hd' hU2 hT ι _ χ hχ a i ha ha' hmax r σ freq hr hrR
    hσmin hσmax hlarge k hQ hfreq hheight
  let U := Z^d
  let D := U^r
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤D := Real.one_le_rpow hU hr
  have hlog : 1≤Real.log D := by
    linarith [abs_nonneg (Real.log A),abs_nonneg (Real.log B)]
  have hL : 1/Real.log D∈Icc (0 : ℝ) 1 :=
    ⟨by positivity,(div_le_one (by linarith)).mpr hlog⟩
  have hp := hprime Z d hZ hd hd' hU2 hT χ hχ a i ha ha' hmax
    r σ freq (1/Real.log D) hr hrR hσmin hσmax hL k hQ hfreq hheight
  have he := herror (χ k) W A B D σ freq Bf hA hD hWs hlarge hBf.le
    (hprofile σ ⟨hσmin,hσmax⟩)
  have hpow : D^ξ≤U^((a-1/2)*r+ε) := by
    dsimp [D]
    rw [←Real.rpow_mul hUp.le]
    apply Real.rpow_le_rpow_of_exponent_le hU
    have hxi : ξ*(R+1)=ε := by dsimp [ξ]; field_simp
    nlinarith [mul_nonneg (show 0≤a-1/2 by linarith) hr,
      mul_le_mul_of_nonneg_right hrR hξ.le]
  have he' : ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
      primePolynomial (χ k) W B D σ freq‖≤E*U^((a-1/2)*r+ε) := by
    apply he.trans
    calc
      _ = E*D^ξ := by dsimp [E]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hE.le
  calc
    _ ≤ ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq‖+
        ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
          primePolynomial (χ k) W B D σ freq‖ := by
      have hid : primePolynomial (χ k) W B D σ freq =
          HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
          (HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
            primePolynomial (χ k) W B D σ freq) := by ring
      conv_lhs => rw [hid]
      exact norm_sub_le _ _
    _ ≤ Cp*U^((a-1/2)*r+ε)+E*U^((a-1/2)*r+ε) := add_le_add hp he'
    _ = _ := by ring

end SevenEighths.HeckePrimeAnnular

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RayOrthogonality
namespace OAI

namespace SevenEighths.RayOrthogonality

open scoped Classical
noncomputable section

section FiniteMonoid
variable {R : Type*} [CommMonoid R] [Finite R]

theorem card_characters (H : Subgroup Rˣ) :
    Fintype.card (characters H) = Nat.card (Rˣ ⧸ H) := by
  rw [← Nat.card_eq_fintype_card]
  exact MulChar.card_subgroupOrderIsoSubgroupMulChar

theorem exists_character_ne_one (H : Subgroup Rˣ) {u : Rˣ} (hu : u ∉ H) :
    ∃ χ : characters H, (χ : MulChar R ℂ) u ≠ 1 := by
  by_contra hn
  apply hu
  have hall : ∀ χ ∈ characters H, χ u = 1 := by
    intro χ hχ
    by_contra h
    exact hn ⟨⟨χ, hχ⟩, h⟩
  have hh := (MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff).mpr hall
  simpa only [characters, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply] using hh

theorem sum_characters_unit (H : Subgroup Rˣ) (u : Rˣ) :
    ∑ χ : characters H, (χ : MulChar R ℂ) u =
      if u ∈ H then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hu : u ∈ H
  · simp only [hu, ite_true]
    calc
      _ = ∑ _χ : characters H, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro χ _
        exact (mem_characters_iff H χ).mp χ.property u hu
      _ = _ := by simp [card_characters]
  · simp only [hu, ite_false]
    obtain ⟨χ, hχ⟩ := exists_character_ne_one H hu
    refine eq_zero_of_mul_eq_self_left hχ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

theorem sum_characters (H : Subgroup Rˣ) (r : R) :
    ∑ χ : characters H, (χ : MulChar R ℂ) r =
      if inUnitSubgroup H r then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hi : inUnitSubgroup H (u : R) ↔ u ∈ H := by
      constructor
      · rintro ⟨v, hv, h⟩
        exact (Units.ext hv) ▸ h
      · exact fun h ↦ ⟨u, rfl, h⟩
    rw [sum_characters_unit, hi]
  · have hn : ¬ inUnitSubgroup H r := by
      rintro ⟨u, rfl, _⟩
      exact hr u.isUnit
    simp only [hn, ite_false]
    exact Finset.sum_eq_zero fun χ _ ↦ MulChar.map_nonunit χ.val hr

theorem ray_card_pos (H : Subgroup Rˣ) : 0 < Nat.card (Rˣ ⧸ H) :=
  Nat.card_pos

end FiniteMonoid

section Residues
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]

omit [Finite (A ⧸ M)] in
theorem inUnitSubgroup_globalUnits_iff (r : A ⧸ M) :
    inUnitSubgroup (globalUnits M) r ↔ principalResidue M r := by
  constructor
  · rintro ⟨u, hur, v, hv⟩
    exact ⟨v, (congrArg Units.val hv).trans hur⟩
  · rintro ⟨u, hu⟩
    exact ⟨Units.map (Ideal.Quotient.mk M).toMonoidHom u, hu, ⟨u, rfl⟩⟩

theorem sum_rayCharacters (r : A ⧸ M) :
    ∑ χ : rayCharacters M, (χ : MulChar (A ⧸ M) ℂ) r =
      if principalResidue M r then (rayCard M : ℂ) else 0 := by
  rw [sum_characters, inUnitSubgroup_globalUnits_iff]

section PrincipalIdeals
variable [IsDomain A] [IsPrincipalIdealRing A]

omit [Finite (A ⧸ M)] in
theorem principalIdeals_iff_generator {I : Ideal A} (hI : I ≠ ⊥) :
    I ∈ principalIdeals M ↔
      principalResidue M (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
  constructor
  · rintro ⟨_, a, ha, u, hu⟩
    have hga : Associated (Submodule.IsPrincipal.generator I) a := by
      rw [← ha]
      exact Submodule.IsPrincipal.associated_generator_span_self a
    obtain ⟨v, hv⟩ := hga
    refine ⟨u * v⁻¹, ?_⟩
    have hq := congrArg (Ideal.Quotient.mk M) hv
    simp only [map_mul] at hq
    simp only [Units.val_mul, map_mul]
    rw [hu, ← hq]
    rw [mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, mul_one]
  · intro h
    exact ⟨hI, _, Ideal.span_singleton_generator I, h⟩

theorem sum_idealCharacters (I : Ideal A) :
    ∑ χ : rayCharacters M, idealCharacter M χ I =
      if I ∈ principalIdeals M then (rayCard M : ℂ) else 0 := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealCharacter, principalIdeals]
  · have heq (χ : rayCharacters M) : idealCharacter M χ I =
        (χ : MulChar (A ⧸ M) ℂ) (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
      exact IdealCharacter.ofResidue_of_generator M χ _ hI (Ideal.span_singleton_generator I)
    simp only [heq, sum_rayCharacters, principalIdeals_iff_generator M hI]

end PrincipalIdeals
end Residues

end
end SevenEighths.RayOrthogonality

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RayQuotient
namespace OAI

namespace SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section

variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)

theorem classNumber_pos : 0 < classNumber M H := ray_card_pos H

include hH

variable [IsDomain A] [IsPrincipalIdealRing A]

omit [Finite (A ⧸ M)] in
theorem identityClass_iff_generator {I : Ideal A} (hI : I ≠ ⊥) :
    I ∈ identityClass M H ↔
      inUnitSubgroup H (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
  constructor
  · rintro ⟨_, a, ha, u, hua, huH⟩
    have hga : Associated (Submodule.IsPrincipal.generator I) a := by
      rw [← ha]
      exact Submodule.IsPrincipal.associated_generator_span_self a
    obtain ⟨v, hv⟩ := hga
    let w := Units.map (Ideal.Quotient.mk M).toMonoidHom v
    refine ⟨u * w⁻¹, ?_, H.mul_mem huH (H.inv_mem (hH ⟨v, rfl⟩))⟩
    have hq := congrArg (Ideal.Quotient.mk M) hv
    simp only [map_mul] at hq
    change (u : A ⧸ M) * ((Units.map (Ideal.Quotient.mk M).toMonoidHom v)⁻¹ :
      (A ⧸ M)ˣ) = _
    rw [hua, ← hq]
    change (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) *
      (w : A ⧸ M) * (w⁻¹ : (A ⧸ M)ˣ) = _
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · intro h
    exact ⟨hI, _, Ideal.span_singleton_generator I, h⟩

theorem sum_idealCharacters (I : Ideal A) :
    ∑ χ : Characters M H, idealCharacter M H hH χ I =
      if I ∈ identityClass M H then (classNumber M H : ℂ) else 0 := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealCharacter, identityClass]
  · have heq (χ : Characters M H) : idealCharacter M H hH χ I =
        (χ : MulChar (A ⧸ M) ℂ) (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
      exact IdealCharacter.ofResidue_of_generator M χ _ hI (Ideal.span_singleton_generator I)
    simp only [heq, sum_characters, identityClass_iff_generator M H hH hI, classNumber]

theorem average_idealCharacters (I : Ideal A) :
    (∑ χ : Characters M H, idealCharacter M H hH χ I) / (classNumber M H : ℂ) =
      if I ∈ identityClass M H then 1 else 0 := by
  rw [sum_idealCharacters]
  have hn : (classNumber M H : ℂ) ≠ 0 := by exact_mod_cast (classNumber_pos M H).ne'
  split_ifs <;> simp [hn]

end
end SevenEighths.RayQuotient

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.RayQuotient
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayQuotient
open HeckeFamily
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

attribute [local instance] OAI.SevenEighths.HeckeRayQuotient.instFiniteQuotientOIdeal_solutions
attribute [local instance] OAI.SevenEighths.HeckeRayQuotient.instIsPrincipalIdealRingO_solutions
theorem idealCoeff_character (χ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (character M H hH χ) I = RayQuotient.idealCharacter M H hH χ I := rfl

theorem average_idealCoeff (I : Ideal O) :
    (RayQuotient.classNumber M H : ℂ)⁻¹ *
      ∑ χ : RayQuotient.Characters M H, idealCoeff (character M H hH χ) I =
      if I ∈ RayQuotient.identityClass M H then 1 else 0 := by
  simp only [idealCoeff_character]
  simpa only [div_eq_mul_inv, mul_comm] using RayQuotient.average_idealCharacters M H hH I

end SevenEighths.HeckeRayQuotient

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeRay
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.HeckePrimeRay
open HeckeFamily HeckePrimeAnnular
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.HeckePrimeRay.instFiniteQuotientOIdeal_solutions
local instance instIsPrincipalIdealRingO_solutions_re169fb_1 : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
theorem finite_average (η : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S.filter (fun I => I∈RayQuotient.identityClass M H), idealCoeff η I*f I) =
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H, ∑ I∈S,
          idealCoeff (twistedFamily M H hH η θ) I*f I := by
  rw [Finset.sum_filter,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [twistedFamily,idealCoeff_product]
  have hs : (∑ θ : RayQuotient.Characters M H,
      idealCoeff η I*idealCoeff (HeckeRayQuotient.character M H hH θ) I*f I) =
      (idealCoeff η I*f I)*∑ θ : RayQuotient.Characters M H,
        idealCoeff (HeckeRayQuotient.character M H hH θ) I := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro θ _
    ring
  rw [hs,mul_left_comm,HeckeRayQuotient.average_idealCoeff M H hH I]
  split_ifs <;> simp

theorem rayPrimePolynomial_eq_average (η : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) :
    rayPrimePolynomial M H η W b D σ freq =
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H,
          primePolynomial (twistedFamily M H hH η θ) W b D σ freq := by
  unfold rayPrimePolynomial
  have hfilter : (annulusSet b D).filter (fun I => Prime I ∧ I∈RayQuotient.identityClass M H) =
      ((annulusSet b D).filter Prime).filter (fun I => I∈RayQuotient.identityClass M H) := by
    ext I
    simp only [Finset.mem_filter]
    tauto
  rw [hfilter,finite_average M H hH η _ (annularWeight W D σ freq)]
  simp only [primePolynomial]
  rw [←Finset.mul_sum]
  ring

theorem rayPrimePolynomial_norm_le (η : Character) (W : ℝ→ℂ) (b D σ freq C : ℝ)
    (hbound : ∀ θ : RayQuotient.Characters M H,
      ‖primePolynomial (twistedFamily M H hH η θ) W b D σ freq‖≤C) :
    ‖rayPrimePolynomial M H η W b D σ freq‖≤C := by
  rw [rayPrimePolynomial_eq_average M H hH η W b D σ freq,norm_mul,norm_inv]
  have hcard : (0 : ℝ)<RayQuotient.classNumber M H := by
    exact_mod_cast RayQuotient.classNumber_pos M H
  have heq : Fintype.card (RayQuotient.Characters M H)=RayQuotient.classNumber M H :=
    RayOrthogonality.card_characters H
  have hn : ‖(RayQuotient.classNumber M H : ℂ)‖=(RayQuotient.classNumber M H : ℝ) := by simp
  rw [hn]
  calc
    _ ≤ (RayQuotient.classNumber M H : ℝ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H, C :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun θ _ => hbound θ)))
        (by positivity)
    _ = C := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,heq]; rw [←mul_assoc,inv_mul_cancel₀ hcard.ne',one_mul]

theorem ray_prime_bin_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (ηrow : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH ηrow θ).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH ηrow) hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, 0≤ r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      (∀ θ : RayQuotient.Characters M H,
        (twistedFamily M H hH ηrow θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖rayPrimePolynomial M H ηrow W B ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨C,hC,hbound⟩ := prime_bin_bound W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ hε he he' hκ hη hbudget
  refine ⟨C,hC,?_⟩
  intro Z d hZ hd hd' hU hT ηrow hχ a i ha ha' hmax r σ freq hr hrR
    hσmin hσmax hlarge hQ hfreq hheight
  apply rayPrimePolynomial_norm_le M H hH
  intro θ
  exact hbound Z d hZ hd hd' hU hT (twistedFamily M H hH ηrow) hχ a i ha ha' hmax
    r σ freq hr hrR hσmin hσmax hlarge θ (hQ θ) hfreq hheight

end SevenEighths.HeckePrimeRay

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeBins
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckePrimeAmplitudeBins

theorem amplitude_bounds (P cap mesh : ℝ) (Q : ℂ) (hcap : 0≤ cap) :
    0≤amplitude P cap mesh Q ∧ amplitude P cap mesh Q≤ cap := by
  unfold amplitude
  split_ifs
  · exact ⟨le_rfl,hcap⟩
  · exact ⟨le_min hcap (le_max_left _ _),min_le_left _ _⟩

theorem amplitude_upper (P cap mesh : ℝ) (Q : ℂ) (hP : 1<P) (hm : 0< mesh)
    (hbound : ‖Q‖≤P^(cap+mesh)) :
    ‖Q‖≤P^(amplitude P cap mesh Q+mesh) := by
  by_cases hQ : Q=0
  · subst Q
    simp only [norm_zero,amplitude,ite_true,zero_add]
    exact Real.rpow_nonneg (by linarith) _
  have hx : 0<‖Q‖ := norm_pos_iff.mpr hQ
  have hl : 0<Real.log P := Real.log_pos hP
  have hd : 0< mesh*Real.log P := mul_pos hm hl
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  by_cases hc : cap≤ max 0 (mesh*(n : ℝ))
  · simpa [amplitude,hQ,n,min_eq_left hc] using hbound
  · have he : amplitude P cap mesh Q=max 0 (mesh*(n : ℝ)) := by
      simp only [amplitude,if_neg hQ]
      exact min_eq_right (le_of_not_ge hc)
    rw [he]
    apply (Real.le_rpow_iff_log_le hx (by linarith : 0<P)).mpr
    have hn : Real.log ‖Q‖/(mesh*Real.log P)<(n : ℝ)+1 := Int.lt_floor_add_one _
    have hn' := (div_lt_iff₀ hd).mp hn
    have hg := mul_le_mul_of_nonneg_right (le_max_right 0 (mesh*(n : ℝ))) hl.le
    nlinarith

theorem amplitude_lower (P cap mesh : ℝ) (Q : ℂ) (hP : 1<P) (hm : 0< mesh)
    (hg : 0<amplitude P cap mesh Q) :
    P^(amplitude P cap mesh Q)≤‖Q‖ := by
  have hQ : Q≠0 := by intro h; simp [amplitude,h] at hg
  have hx : 0<‖Q‖ := norm_pos_iff.mpr hQ
  have hl : 0<Real.log P := Real.log_pos hP
  have hd : 0< mesh*Real.log P := mul_pos hm hl
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  have hpos : 0< mesh*(n : ℝ) := by
    have hmin : amplitude P cap mesh Q≤ max 0 (mesh*(n : ℝ)) := by
      simp only [amplitude,if_neg hQ]
      exact min_le_right _ _
    have ht : 0< max 0 (mesh*(n : ℝ)) := hg.trans_le hmin
    exact (lt_max_iff.mp ht).resolve_left (lt_irrefl _)
  have he : amplitude P cap mesh Q=min cap (mesh*(n : ℝ)) := by
    simp only [amplitude,if_neg hQ]
    rw [max_eq_right hpos.le]
  have hn : (n : ℝ)≤Real.log ‖Q‖/(mesh*Real.log P) := Int.floor_le _
  have hn' := (le_div_iff₀ hd).mp hn
  have hb : amplitude P cap mesh Q*Real.log P≤Real.log ‖Q‖ := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_right (min_le_right cap (mesh*(n : ℝ))) hl.le
    nlinarith
  have hpow : 0<P^(amplitude P cap mesh Q) := Real.rpow_pos_of_pos (by linarith) _
  apply (Real.log_le_log_iff hpow hx).mp
  rw [Real.log_rpow (by linarith : 0<P)]
  exact hb

theorem squared_spike (U w cap mesh : ℝ) (Q : ℂ) (hU : 1<U) (hw : 0<w)
    (hm : 0< mesh) (hg : 0<amplitude (U^w) cap mesh Q) :
    U^(2*w*amplitude (U^w) cap mesh Q)≤‖Q‖^2 := by
  have hP : 1<U^w := Real.one_lt_rpow hU hw
  have hb := amplitude_lower (U^w) cap mesh Q hP hm hg
  have hs := (sq_le_sq₀ (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _) (norm_nonneg _)).mpr hb
  convert (preTransparency := .instances) hs using 1
  rw [←Real.rpow_natCast,←Real.rpow_mul (Real.rpow_nonneg (by linarith : (0 : ℝ)≤U) _),
    ←Real.rpow_mul (by linarith : (0 : ℝ)≤U)]
  congr 1
  ring

end SevenEighths.HeckePrimeAmplitudeBins

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeScale
namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeAmplitudeBins

theorem upper_allowance_eventually (C dmin rmin ε mesh : ℝ)
    (hd : 0<dmin) (hmesh : 0< mesh) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r cap : ℝ, dmin≤d → rmin≤ r →
      C*(Z^d)^(cap*r+ε)≤((Z^d)^r)^(cap+mesh) := by
  have hh := HeckeDyadic.constant_absorbed_eventually C (dmin*(rmin*mesh-ε))
    (mul_pos hd (by linarith))
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ
  intro d r cap hd' hr'
  have hZp : 0<Z := by linarith
  have hU : 0<Z^d := Real.rpow_pos_of_pos hZp _
  have hgr : rmin*mesh-ε≤ r*mesh-ε := by nlinarith
  have hexp : dmin*(rmin*mesh-ε)≤d*(r*mesh-ε) :=
    mul_le_mul hd' hgr (by linarith) (hd.trans_le hd').le
  have hc : C≤(Z^d)^(r*mesh-ε) := by
    apply hC.trans
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  calc
    _ ≤ (Z^d)^(r*mesh-ε)*(Z^d)^(cap*r+ε) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hU.le _)
    _ = ((Z^d)^r)^(cap+mesh) := by
      rw [←Real.rpow_add hU,←Real.rpow_mul hU.le]
      congr 1
      ring

theorem actual_bins_eventually (C dmin rmin ε mesh : ℝ)
    (hd : 0<dmin) (hr : 0< rmin) (hmesh : 0< mesh) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → ∀ r cap : ℝ, rmin≤ r → 0≤ cap →
      ∀ Q : ℂ, ‖Q‖≤C*(Z^d)^(cap*r+ε) →
      0≤amplitude ((Z^d)^r) cap mesh Q ∧
      amplitude ((Z^d)^r) cap mesh Q≤ cap ∧
      amplitude ((Z^d)^r) cap mesh Q∈labels cap mesh ∧
      ‖Q‖≤((Z^d)^r)^(amplitude ((Z^d)^r) cap mesh Q+mesh) ∧
      (0<amplitude ((Z^d)^r) cap mesh Q →
        (Z^d)^(2*r*amplitude ((Z^d)^r) cap mesh Q)≤‖Q‖^2) := by
  filter_upwards [upper_allowance_eventually C dmin rmin ε mesh hd hmesh hgap,
    eventually_gt_atTop (1 : ℝ)] with Z hallow hZ
  intro d hd' r cap hr' hcap Q hQ
  have hU : 1<Z^d := Real.one_lt_rpow hZ (hd.trans_le hd')
  have hP : 1<(Z^d)^r := Real.one_lt_rpow hU (hr.trans_le hr')
  have hb := amplitude_bounds ((Z^d)^r) cap mesh Q hcap
  exact ⟨hb.1,hb.2,amplitude_mem_labels _ cap mesh Q hmesh,
    amplitude_upper _ cap mesh Q hP hmesh (hQ.trans (hallow d r cap hd' hr')),
    squared_spike (Z^d) r cap mesh Q hU (hr.trans_le hr') hmesh⟩

end SevenEighths.HeckePrimeAmplitudeBins

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeScale
namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeScale
open HeckeFamily

theorem log_scale_eventually (dmin rmin K : ℝ) (hd : 0<dmin) (hr : 0< rmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r : ℝ, dmin≤d → rmin≤ r →
      K≤Real.log ((Z^d)^r) := by
  have hlog : ∀ᶠ Z : ℝ in atTop, max 0 (K/(dmin*rmin))≤Real.log Z :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlog,eventually_ge_atTop (1 : ℝ)] with Z hlog hZ
  intro d r hd' hr'
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [Real.log_rpow (Real.rpow_pos_of_pos hZp _),Real.log_rpow hZp]
  have hp : 0<dmin*rmin := mul_pos hd hr
  have hk : K≤dmin*rmin*Real.log Z := by
    have hh := (div_le_iff₀ hp).mp ((le_max_right 0 _).trans hlog)
    nlinarith
  have hprod : dmin*rmin≤d*r := mul_le_mul hd' hr' hr.le (hd.trans_le hd').le
  have hl : 0≤Real.log Z := (le_max_left _ _).trans hlog
  nlinarith [mul_le_mul_of_nonneg_right hprod hl]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.HeckePrimeScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeActual
namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckePrimeAmplitudeActual
open HeckeFamily HeckePrimeRay HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.HeckePrimeAmplitudeActual.instFiniteQuotientOIdeal
theorem ray_amplitude_bins_oai (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (χ : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH χ) hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, rmin≤ r → r≤R → σmin≤σ → σ≤σmax →
      (∀ θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  obtain ⟨C,hC,hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ hε he he' hκ hη hbudget
  have hbins := actual_bins_eventually C dmin rmin ε mesh hdmin hrmin hmesh hgap
  have hlog := HeckePrimeScale.log_scale_eventually dmin rmin
    (2*(|Real.log A|+|Real.log B|)+1) hdmin hrmin
  filter_upwards [hbins,hlog,eventually_ge_atTop (1 : ℝ)] with Z hb hl hZ
  intro d hd hd' hU hT χ hχ a i ha ha' hmax r σ freq hr hr' hσ hσ' hQ hf ht
  have hestimate := hbound Z d hZ (hdmin.trans_le hd).le hd' hU hT χ hχ a i
    ha ha' hmax r σ freq (hrmin.trans_le hr).le hr' hσ hσ' (hl d r hd hr) hQ hf ht
  exact hb d hd r (a-1/2) hr (by linarith) _ hestimate

end SevenEighths.HeckePrimeAmplitudeActual

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.HeckePrimeAmplitudeActual.ray_amplitude_bins_oai := @OAI.SevenEighths.HeckePrimeAmplitudeActual.ray_amplitude_bins_oai
