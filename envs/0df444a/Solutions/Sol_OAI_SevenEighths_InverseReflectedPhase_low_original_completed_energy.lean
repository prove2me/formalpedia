-- Prove2me | solution 1 for OAI.SevenEighths.InverseReflectedPhase.low_original_completed_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:28:51.404658+00:00
-- url     : https://prove2.me/submissions/732a76ca-b1d1-4897-8ea7-48ceb6580e88

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_low_original_inactive_energy
import Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_original_completed_residual_source

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
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

namespace CompletedGauss

section

open ActualEisensteinCubic ConcreteTraceCRT

theorem cubeWeight_zero_of_mask (Ψ : O →* ℂ) (I : Ideal O)
    (h : Ψ (primaryGenerator I) = 0) : cubeWeight Ψ I = 0 := by
  change _ * Ψ (primaryGenerator I) ^ 3 / _ = 0
  rw [h, zero_pow (by decide), mul_zero, zero_div]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
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

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter

open scoped BigOperators Classical

namespace DescentWeightedCauchy

theorem weighted_cauchy_sq {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ^ 2 ≤
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have hnorm : ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      ∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖ := by
    simpa only [norm_mul, norm_star] using
      norm_sum_le s (fun i => w i * U i * star (V i))
  calc
    _ ≤ (∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => by positivity)) |>.mpr hnorm
    _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i _ => by positivity) (fun i _ => by positivity)
      (fun i _ => by ring_nf; exact le_rfl)

end DescentWeightedCauchy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CubeLabels
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

namespace QuadraticMainBoundary
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open QuadraticSquarefreeKernel

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_le_of_dvd {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ Ideal.absNorm J := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_iff_ne_zero.mpr (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm hIJ)

end QuadraticMainBoundary

open scoped BigOperators Classical

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

lemma divisorDyadicScale_ge_one (j : ℕ) : 1 ≤ divisorDyadicScale j := le_max_left _ _

theorem divisorDyadicBin_bounds (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (D : Ideal O) (hD : D ∈ divisorDyadicBin S N j) :
    divisorDyadicScale j.val ≤ (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ 2 * divisorDyadicScale j.val := by
  obtain ⟨hDS,hj⟩ := Finset.mem_filter.mp hD
  have hd := hS D hDS
  have hb := divisorDyadicLabel_bounds N D hd.1 hd.2
  rw [hj] at hb
  refine ⟨max_le hd.1 hb.1.le, ?_⟩
  have hm : (2 : ℝ)^j.val/2 ≤ divisorDyadicScale j.val := le_max_right _ _
  linarith [hb.2]

theorem divisorDyadicBin_scale_le (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (hj : (divisorDyadicBin S N j).Nonempty) :
    divisorDyadicScale j.val ≤ N := by
  obtain ⟨D,hD⟩ := hj
  exact (divisorDyadicBin_bounds S N hS j D hD).1.trans (hS D (Finset.mem_filter.mp hD).1).2

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.PowerfulParts
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
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid

theorem rowPowerfulPart_ne_zero (I : Ideal O) : rowPowerfulPart I≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem rowPowerfulPart_powerful (I : Ideal O) : PowerfulIdeal (rowPowerfulPart I) := by
  refine ⟨rowPowerfulPart_ne_zero I,?_⟩
  intro P hP
  rw [normalizedFactors_rowPowerfulPart] at hP ⊢
  have hp := (Multiset.mem_filter.mp hP).2
  rw [Multiset.count_filter,if_pos hp]
  exact hp

end

open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid

theorem squarefreeMaskPart_ne_zero (I R : Ideal O) : squarefreeMaskPart I R≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem squarefreeMaskPart_dvd (I R : Ideal O) (hI : Squarefree I) : squarefreeMaskPart I R∣R := by
  by_cases hR : R=0
  · rw [hR]; exact dvd_zero _
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (squarefreeMaskPart_ne_zero I R) hR).mpr
  rw [normalizedFactors_squarefreeMaskPart]
  apply Multiset.le_iff_count.mpr
  intro P
  rw [Multiset.count_filter]
  split_ifs with hp
  · have hn := Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI) P
    by_cases hz : (normalizedFactors I).count P=0
    · omega
    · have hm := Multiset.count_pos.mp (Nat.pos_of_ne_zero hz)
      have hr := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hR).mpr ⟨prime_of_normalized_factor P hm,hp⟩
      have hc := Multiset.count_pos.mpr hr
      omega
  · omega

theorem rowMaskPart_dvd (I R : Ideal O) : rowMaskPart I R∣R :=
  squarefreeMaskPart_dvd _ _ (rowSimplePart_squarefree I)

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.DirichletForm
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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve

theorem rowResidualPart_injective_on_fiber (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hS : ∀I∈S,I≠0) : Set.InjOn (fun I => rowResidualPart I Q) (completedRowFiber S Q A T) := by
  intro I hI J hJ he
  change rowResidualPart I Q=rowResidualPart J Q at he
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
  calc
    I = rowPowerfulPart I*rowMaskPart I Q*rowResidualPart I Q := (row_powerful_mask_residual_product I Q (hS I hIS)).symm
    _ = rowPowerfulPart J*rowMaskPart J Q*rowResidualPart J Q := by rw [hIA,hJA,hIT,hJT,he]
    _ = J := row_powerful_mask_residual_product J Q (hS J hJS)

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CanonicalQuadraticSieve

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff

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
namespace CompletedGauss

section
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid

theorem completed_branch_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(I : Ideal O),I≠0 → ∀{ι : Type*} [Fintype ι]
      (P : ι→Ideal O) [∀i,(P i).IsMaximal],Function.Injective P →
      (∀i,P i∣I) → (6:ℝ)^(2*Fintype.card ι)≤C*(Ideal.absNorm I:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/6) (by positivity)
  refine ⟨C ^6,by positivity,?_⟩
  intro I hI ι _ P _ hinj hd
  let f : ι→primeSupport I := fun i => ⟨P i,by
    change P i∈(normalizedFactors I).toFinset
    exact Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr
      ⟨Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance,hd i⟩)⟩
  have hfi : Function.Injective f := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hcard : Fintype.card ι≤(primeSupport I).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hfi
  have htwo : (2:ℝ)^Fintype.card ι≤C*(Ideal.absNorm I:ℝ)^(ε/6) :=
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard).trans (hbound I hI)
  have hn : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  calc
    _ = (36:ℝ)^Fintype.card ι := by rw [pow_mul]; norm_num
    _ ≤ (64:ℝ)^Fintype.card ι := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = ((2:ℝ)^Fintype.card ι)^6 := by rw [←pow_mul, Nat.mul_comm, pow_mul]; norm_num
    _ ≤ (C*(Ideal.absNorm I:ℝ)^(ε/6))^6 := pow_le_pow_left₀ (by positivity) htwo 6
    _ = C ^6*(Ideal.absNorm I:ℝ)^ε := by
      rw [mul_pow,←Real.rpow_mul_natCast hn.le]
      congr 2
      ring

end

open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum

theorem sum_completedRowFibers (S : Finset (Ideal O)) (Q : Ideal O) (f : Ideal O→ℝ) :
    (∑A∈S.image rowPowerfulPart,∑T∈S.image (fun I => rowMaskPart I Q),
      ∑I∈completedRowFiber S Q A T,f I)=∑I∈S,f I := by
  let mapPair : Ideal O→Ideal O×Ideal O := fun I => (rowPowerfulPart I,rowMaskPart I Q)
  have hm : ∀I∈S,mapPair I∈(S.image rowPowerfulPart)×ˢ(S.image (fun J => rowMaskPart J Q)) := by
    intro I hI
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hI,Finset.mem_image_of_mem _ hI⟩
  have hh := Finset.sum_fiberwise_of_maps_to hm f
  rw [Finset.sum_product] at hh
  simpa only [mapPair,Prod.mk.injEq,completedRowFiber] using hh

theorem rowMaskPart_image_card (S : Finset (Ideal O)) (Q : Ideal O) (hQ : Q≠0) :
    (S.image (fun I => rowMaskPart I Q)).card≤(idealDivisors Q).card := by
  apply Finset.card_le_card
  intro T hT
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hT
  exact (mem_idealDivisors hQ).mpr (rowMaskPart_dvd I Q)

end CompletedGauss

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.SupportBounds
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

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem columnWeight_zero_of_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P I : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPI : P∣I) (hm : m∈P) :
    columnWeight (rowTwist Ψ m f z) I = 0 := by
  unfold columnWeight
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryGenerator I=0
  · rw [hg]
    change squarefreeGaussCoefficient I * (Ψ 0 * idealRowHom _ (Ideal.span {0})) = 0
    rw [Ideal.span_singleton_zero]
    change squarefreeGaussCoefficient I * (Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O)) = 0
    rw [map_zero (idealRowHom _),mul_zero,mul_zero]
  · change squarefreeGaussCoefficient I *
      (Ψ (primaryGenerator I) * idealRowHom _ (Ideal.span {primaryGenerator I})) = 0
    rw [(primaryGenerator_spec I hg).1,idealRowHom_zero_of_dvd _ hP hPI hx,mul_zero,mul_zero]

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open CompletedGauss hiding O

end CanonicalRowCompletion

open scoped BigOperators Classical
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.LogSeparation
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

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem rowTwist_primary_zero_of_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    rowTwist Ψ m f z (primaryGenerator B) = 0 := by
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryGenerator B=0
  · rw [hg]
    change Ψ 0 * idealRowHom _ (Ideal.span {(0:ActualEisensteinCubic.O)}) = 0
    rw [Ideal.span_singleton_zero]
    change Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O) = 0
    rw [map_zero (idealRowHom _),mul_zero]
  · change Ψ (primaryGenerator B) * idealRowHom _ (Ideal.span {primaryGenerator B}) = 0
    rw [(primaryGenerator_spec B hg).1,idealRowHom_zero_of_dvd _ hP hPB hx,mul_zero]

theorem cubeWeight_zero_of_prime_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    cubeWeight (rowTwist Ψ m f z) B = 0 :=
  cubeWeight_zero_of_mask _ B (rowTwist_primary_zero_of_mask Ψ m f z hP hPB hm)

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O

end

open ActualEisensteinCubic
open CompletedGauss hiding O

end CanonicalRowCompletion

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.FiniteTranslations
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

namespace CubicEisenstein

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

lemma finiteAdditiveFourierCoeff_norm {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (hφ : ∀x,‖φ x‖≤1) (h : R) :
    ‖finiteAdditiveFourierCoeff ψ φ h‖≤1 := by
  have hN : (0:ℝ)<Fintype.card R:=by exact_mod_cast Fintype.card_pos
  rw [finiteAdditiveFourierCoeff,norm_div,Complex.norm_natCast]
  apply (div_le_one hN).mpr
  calc
    _ ≤ ∑x,‖φ x*ψ (-h*x)‖ := norm_sum_le _ _
    _ ≤ ∑_x : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [norm_mul,AddChar.norm_apply,mul_one] using hφ x
    _ = _ := by simp

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedThetaTwist_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : lambda^2∣x-1) :
    fixedThetaTwist Ψ x=eisEmbedding (symbol ramifiedTraceLambda x)*Ψ x := by
  simp only [fixedThetaTwist,if_pos hx]

lemma fixedThetaTwist_not_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : ¬lambda^2∣x-1) :
    fixedThetaTwist Ψ x=0 := by
  simp only [fixedThetaTwist,if_neg hx]

lemma paperLambda_symbol_cube (x : Eis) (hx : lambda^2∣x-1) :
    (eisEmbedding (symbol ramifiedTraceLambda x))^3=1 := by
  rw [←map_pow,symbol_cube_of_isCoprime _ _ hx
    (ramified_character_coprime 0 1 _ x (Or.inl (by simp)) hx),map_one]

lemma paperLambda_symbol_norm (x : Eis) (hx : lambda^2∣x-1) :
    ‖eisEmbedding (symbol ramifiedTraceLambda x)‖=1 := by
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one,one_pow] using congrArg norm (paperLambda_symbol_cube x hx)

lemma fixedThetaTwist_norm_le_one (Ψ : Eis→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1) (x : Eis) :
    ‖fixedThetaTwist Ψ x‖≤1 := by
  by_cases hx : lambda^2∣x-1
  · rw [fixedThetaTwist_primary Ψ x hx,norm_mul,paperLambda_symbol_norm x hx,one_mul]
    exact hΨ x
  · rw [fixedThetaTwist_not_primary Ψ x hx,norm_zero]
    norm_num

lemma fixedThetaQuotient_norm_le_one (Ψ : Eis→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1)
    (c : Eis) (x : Eis⧸Ideal.span {c}) : ‖fixedThetaQuotient Ψ c x‖≤1 :=
  fixedThetaTwist_norm_le_one Ψ hΨ _

end

open ActualEisensteinCubic CompletedGauss CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.PeriodicRows
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

open scoped BigOperators Classical

namespace CompletedGauss

section
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma completedReflectionPool_odd (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    ringChar (Eis⧸P.val)≠2 := (Finset.mem_filter.mp P.property).2.2.1

lemma completedReflectionPool_divides (I Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (P:completedReflectionPool I Q) : P.val∣I*Q :=
  ((mem_completedReflectionPool I Q P.val hI hQ).mp P.property).2.1

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedConductor
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

open scoped Classical

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma basePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖basePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:BasePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedThetaTwists
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
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedThetaRowCoeff_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (h:Eis⧸Ideal.span {c}) :
    ‖fixedThetaRowCoeff c hc φ h‖≤1 :=
  finiteAdditiveFourierCoeff_norm _ _ (fixedThetaQuotient_norm_le_one φ hφ c) h

end CubicEisenstein

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma pool_odd (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ringChar (Eis⧸P.val)≠2 :=
  completedReflectionPool_odd I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_divides (I Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (P:pool I Q Q0) : P.val∣I*Q :=
  completedReflectionPool_divides I Q hI hQ ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_free (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ¬Q0≤P.val :=
  (Finset.mem_filter.mp P.property).2

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ReflectionFibers
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

open scoped Classical BigOperators

open scoped BigOperators Classical

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma representativeRowFiber_injective (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (hrows:∀J∈rows,J≠0) :
    Set.InjOn (fun J=>rowResidualPart J Q) (representativeRowFiber rows I Q) :=
  rowResidualPart_injective_on_fiber rows Q (rowPowerfulPart I) (rowMaskPart I Q) hrows

end

open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

open scoped Classical BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ResidualEquivalence
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

open scoped BigOperators Classical ContDiff

open scoped BigOperators Classical MatrixGroups

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion

section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)

lemma numeratorFactor_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖(Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
      D.numeratorSupported) n‖≤1 := by
  change ‖Ψ n*numeratorBadTwist _ _ _ _ _ n‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans (numeratorBadTwist_norm _ _ _ _ _ n)

lemma fixedFactor_norm (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖D.fixedFactor Ψ Q n‖≤1 := by
  change ‖((Ψ*numeratorBadTwist _ _ _ _ _) n)*(basePrimeRow _ _ _ n)‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (D.numeratorFactor_norm Ψ hΨ n)).trans (basePrimeRow_norm _ _ _ n)

lemma fixedCoefficient_norm (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hΨ:∀n,‖Ψ n‖≤1)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})] (h:Eis⧸Ideal.span {c}) :
    ‖fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h‖≤1 :=
  fixedThetaRowCoeff_norm c hc _ (D.fixedFactor_norm Ψ Q hΨ) h

end GoodMaskRowData

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.TerminalWidths
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseTerminalWidths
open ActualEisensteinCubic CompletedGauss UniqueFactorizationMonoid
open InverseMoment CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma norm_one_le (I : Ideal O) (hI : I ≠ 0) : (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem normWidth_nonneg (Z : ℝ) (hZ : 1 < Z) (I : Ideal O) (hI : I ≠ 0) :
    0 ≤ normWidth Z I := Real.logb_nonneg hZ (norm_one_le I hI)

end SevenEighths.InverseTerminalWidths

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.CanonicalPool
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma maximal_coprime_of_not_dvd (P J : Ideal Eis) [P.IsMaximal] (h : ¬P∣J) : IsCoprime P J := by
  rw [Ideal.isCoprime_iff_codisjoint]
  apply ((Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint).mp
  exact fun hle => h (Ideal.dvd_iff_le.mpr hle)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.MarkedLevel
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma PrimeFamily.level_coprime {ι : Type*} (P : PrimeFamily ι)
    (Q : Ideal Eis) (c : Eis) (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q)
    (hQ : ∀ i, IsCoprime Q (P.ideal i)) (i : ι) :
    IsCoprime (Ideal.span {(9:Eis)*c}) (P.ideal i) := by
  have h9 : IsCoprime (Ideal.span {(9:Eis)}) (P.ideal i) := by
    rw [← P.generator_span i]
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (ShortDraftCRT.primary_coprime_nine _ (P.generator_primary i)).symm
  rw [← Ideal.span_singleton_mul_span_singleton,hcQ]
  exact h9.mul_left (h9.mul_left (hQ i))

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.InactiveAggregation
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem original_pool_choice_count (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (R Q Q₀ : Ideal Eis), R≠0 → Q≠0 →
      (Fintype.card (FreeReflection.pool R Q Q₀→Fin 6):ℝ)^2≤C*(Ideal.absNorm (R*Q):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := completed_branch_count_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro R Q Q₀ hR hQ
  let (P : FreeReflection.pool R Q Q₀) : P.val.IsMaximal := FreeReflection.pool_maximal R Q Q₀ P
  have hh := hbound (R*Q) (mul_ne_zero hR hQ) (fun P : FreeReflection.pool R Q Q₀ => P.val)
    Subtype.val_injective (FreeReflection.pool_divides R Q Q₀ hR hQ)
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,← pow_mul,
    Nat.mul_comm (Fintype.card (FreeReflection.pool R Q Q₀)) 2] using hh
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma weighted_finite_row_energy {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤
      (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*(∑ k∈rows, ‖f i k‖^2) := by
  calc
    _ ≤ ∑ k∈rows, (∑ i∈L, ‖w i‖*‖f i k‖^2)*(∑ i∈L, ‖w i‖) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [star_one,mul_one,norm_one,one_pow] using
        DescentWeightedCauchy.weighted_cauchy_sq L w (fun i => f i k) (fun _ => 1)
    _ = _ := by
      rw [← Finset.sum_mul,Finset.sum_comm]
      simp only [← Finset.mul_sum]
      ring

lemma weighted_finite_row_energy_uniform {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) (B : ℝ)
    (hf : ∀ i∈L, (∑ k∈rows, ‖f i k‖^2)≤B) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤(∑ i∈L, ‖w i‖)^2*B := by
  apply (weighted_finite_row_energy L rows w f).trans
  calc
    _ ≤ (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*B := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i hi => norm_nonneg _))
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hf i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.RowReindex
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem original_fiber_sum_reindex {M : Type*} [AddCommMonoid M]
    (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (f : Ideal Eis→M) :
    (∑ I∈representativeRowFiber rows R Q,f I)=
      ∑ K∈originalResidualRows rows R Q,f (reconstructFiberRow R Q K) := by
  rw [originalResidualRows,Finset.sum_image (representativeRowFiber_injective rows R Q hrows)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [reconstructFiberRow_of_original rows R Q I hI (hrows I (Finset.mem_filter.mp hI).1)]

theorem original_fiber_energy_reindex (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (f : Ideal Eis→ℂ) :
    (∑ I∈representativeRowFiber rows R Q,‖f I‖^2)=
      ∑ K∈originalResidualRows rows R Q,‖f (reconstructFiberRow R Q K)‖^2 :=
  original_fiber_sum_reindex rows R Q hrows (fun I => ‖f I‖^2)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.PoolArithmetic
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma poolPrimeFamily_period (R Q Q₀ : Ideal Eis) (P : FreeReflection.pool R Q Q₀) :
    IsCoprime Q₀ ((poolPrimeFamily R Q Q₀).ideal P) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro h
  exact FreeReflection.pool_free R Q Q₀ P (Ideal.dvd_iff_le.mp h)

lemma poolPrimeFamily_odd (R Q Q₀ : Ideal Eis) (P : FreeReflection.pool R Q Q₀) :
    ringChar (Eis⧸(poolPrimeFamily R Q Q₀).ideal P)≠2 := FreeReflection.pool_odd R Q Q₀ P

lemma poolPrimeFamily_fiber_row_coprime (R I Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    IsCoprime ((poolPrimeFamily R Q Q₀).ideal P) (rowResidualPart I Q) := by
  apply maximal_coprime_of_not_dvd
  exact FreeReflection.pool_nonresidual I Q Q₀
    (nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask P)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.CellArithmetic
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma residual_level_coprime (K Q₀ : Ideal Eis) (hK : Admissible K)
    (c : Eis) (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) (hcop : IsCoprime Q₀ K) :
    IsCoprime (Ideal.span {(9:Eis)*c}) K := by
  rw [←PrimeFamily.residual_product K hK]
  apply IsCoprime.prod_right_iff.mpr
  intro i hi
  exact (PrimeFamily.residual K hK).level_coprime Q₀ c hc
    (fun i => hcop.of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK i)) i

variable {φ σ : Type*} [Fintype σ] [DecidableEq σ]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.PowerfulBudget
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseReflectedPhasePowerfulBudget
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem powerful_half_norm_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (X : ℝ),1≤X →
      (∀ I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∑ I∈S,(Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤ C*X^ε := by
  let δ := ε/2
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hcount⟩ := powerful_ideal_count δ hδ
  let C := D*(2:ℝ)^(1/2+δ)*(2+1/(δ*Real.log 2))
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro S X hX hS
  have hx : 0<X := zero_lt_one.trans_le hX
  have hnorm (I : Ideal O) (hI : I∈S) :
      1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤X :=
    ⟨QuadraticMainBoundary.norm_one_le (hS I hI).1.1,(hS I hI).2⟩
  have hbin (j : Fin (columnDyadicLength X+1)) :
      ∑ I∈divisorDyadicBin S X j,(Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤
        D*(2:ℝ)^(1/2+δ)*X^δ := by
    let R := divisorDyadicScale j.val
    have hR : 1≤R := divisorDyadicScale_ge_one _
    have hr : 0<R := zero_lt_one.trans_le hR
    by_cases he : (divisorDyadicBin S X j).Nonempty
    · have hRX : R≤X := divisorDyadicBin_scale_le S X hnorm j he
      have hc : ((divisorDyadicBin S X j).card:ℝ) ≤ D*(2*R)^(1/2+δ) := by
        apply hcount _ _ (by linarith)
        intro I hI
        exact ⟨(hS I (Finset.mem_filter.mp hI).1).1,
          (divisorDyadicBin_bounds S X hnorm j I hI).2⟩
      have hw (I : Ideal O) (hI : I∈divisorDyadicBin S X j) :
          (Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤ R^(-1/2:ℝ) :=
        Real.rpow_le_rpow_of_nonpos hr (divisorDyadicBin_bounds S X hnorm j I hI).1
          (by norm_num)
      calc
        _ ≤ ((divisorDyadicBin S X j).card:ℝ)*R^(-1/2:ℝ) := by
          apply (Finset.sum_le_sum hw).trans_eq
          simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ (D*(2*R)^(1/2+δ))*R^(-1/2:ℝ) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hr.le _)
        _ = (D*(2:ℝ)^(1/2+δ))*(R^(1/2+δ)*R^(-1/2:ℝ)) := by
          rw [Real.mul_rpow (by norm_num) hr.le]
          ring
        _ = D*(2:ℝ)^(1/2+δ)*R^δ := by
          rw [←Real.rpow_add hr]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hRX hδ.le) (by positivity)
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      positivity
  rw [sum_divisorDyadicBins S X]
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength X+1),D*(2:ℝ)^(1/2+δ)*X^δ :=
      Finset.sum_le_sum (fun j _=>hbin j)
    _ = (columnDyadicLength X+1:ℝ)*(D*(2:ℝ)^(1/2+δ)*X^δ) := by simp
    _ ≤ ((2+1/(δ*Real.log 2))*X^δ)*(D*(2:ℝ)^(1/2+δ)*X^δ) :=
      mul_le_mul_of_nonneg_right (columnDyadicLength_small_power δ hδ X hX) (by positivity)
    _ = C*X^ε := by
      calc
        _ = C*(X^δ*X^δ) := by dsimp [C];ring
        _ = _ := by rw [←Real.rpow_add hx,show δ+δ=ε by dsimp [δ];ring]

lemma rowPowerful_norm_le (I : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowPowerfulPart I):ℝ) ≤ Ideal.absNorm I := by
  apply QuadraticMainBoundary.norm_le_of_dvd hI
  exact ⟨rowSimplePart I,(row_powerful_simple_product I hI).symm⟩

theorem row_mask_powerful_budget (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z : ℝ),2≤Z → ∀ (S : Finset (Ideal O)) (Q : Ideal O),
      (∀ I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤Z^L →
      ((S.image (fun I=>rowMaskPart I Q)).card:ℝ)*
        (∑ A∈S.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-1/2:ℝ)) ≤ C*Z^ε := by
  let δ := ε/(2*(L+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨Cp,hCp,hpower⟩ := powerful_half_norm_sum δ hδ
  obtain ⟨Cd,hCd,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨Cd*Cp,mul_pos hCd hCp,?_⟩
  intro Z hZ S Q hS hQ hQN
  have hz : 0<Z := by linarith
  have hX : 1≤Z^L := Real.one_le_rpow (by linarith) hL
  have hp : (∑ A∈S.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-1/2:ℝ)) ≤ Cp*(Z^L)^δ := by
    apply hpower _ _ hX
    intro A hA
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨rowPowerfulPart_powerful I,(rowPowerful_norm_le I (hS I hI).1).trans (hS I hI).2⟩
  have hm : ((S.image (fun I=>rowMaskPart I Q)).card:ℝ) ≤ Cd*(Z^L)^δ :=
    ((Nat.cast_le.mpr (rowMaskPart_image_card S Q hQ)).trans (hdiv Q hQ)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hQN hδ.le) hCd.le)
  have he : L*(δ+δ) ≤ ε := by
    have heq : δ*(2*(L+1))=ε := by dsimp [δ];field_simp
    nlinarith
  calc
    _ ≤ (Cd*(Z^L)^δ)*(Cp*(Z^L)^δ) :=
      mul_le_mul hm hp (Finset.sum_nonneg (fun A _=>Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)
    _ = (Cd*Cp)*((Z^L)^δ*(Z^L)^δ) := by ring
    _ = (Cd*Cp)*Z^(L*(δ+δ)) := by
      rw [←Real.rpow_add (Real.rpow_pos_of_pos hz L),←Real.rpow_mul hz.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) he) (mul_pos hCd hCp).le

end SevenEighths.InverseReflectedPhasePowerfulBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.CompletedAggregation
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem completed_representative_aggregation (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z : ℝ),2≤Z → ∀ (parents : Finset (Ideal Eis)) (Q : Ideal Eis),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤Z^L →
      ∀ (E : ℝ) (f : Ideal Eis→ℝ),0≤E →
      (∀ J∈parents,(∑ I∈representativeRowFiber parents J Q,f I)≤
        E*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ))) →
      (∑ I∈parents,f I)≤C*Z^ε*E := by
  obtain ⟨C,hC,hbudget⟩ := InverseReflectedPhasePowerfulBudget.row_mask_powerful_budget L ε hL hε
  refine ⟨C,hC,?_⟩
  intro Z hZ parents Q hparents hQ hQN E f hE hf
  have hb := hbudget Z hZ parents Q hparents hQ hQN
  simp only [neg_div] at hb
  have hblocks (A T : Ideal Eis) : (∑ I∈completedRowFiber parents Q A T,f I)≤
      E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) := by
    by_cases he : (completedRowFiber parents Q A T).Nonempty
    · obtain ⟨J,hJ⟩ := he
      obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
      have hh := hf J hJS
      simpa only [representativeRowFiber,hJA,hJT] using hh
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      exact mul_nonneg hE (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [←sum_completedRowFibers parents Q f]
  calc
    _ ≤ ∑ A∈parents.image rowPowerfulPart,∑ _T∈parents.image (fun I => rowMaskPart I Q),
          E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) :=
      Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun T _ => hblocks A T))
    _ = (((parents.image (fun I => rowMaskPart I Q)).card:ℝ)*
          (∑ A∈parents.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-(1/2:ℝ))))*E := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hE
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.OriginalWeights
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma one_sub_inverse_norm_le_one (I : Ideal Eis) (hI : I≠0) :
    ‖1-(Ideal.absNorm I:ℂ)⁻¹‖≤1 := by
  have hn : (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hi : (Ideal.absNorm I:ℝ)⁻¹≤1 := inv_le_one_of_one_le₀ hn
  have he : (1-(Ideal.absNorm I:ℂ)⁻¹)=((1-(Ideal.absNorm I:ℝ)⁻¹):ℝ) := by push_cast;rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  have hp : 0≤(Ideal.absNorm I:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  linarith

lemma frozenInactiveWeight_norm (J F Q Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J Q Q₀)) :
    ‖frozenInactiveWeight J F Q Q₀ A‖≤1 := by
  unfold frozenInactiveWeight
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro b hb
    exact norm_nonneg _
  · intro b hb
    split_ifs
    · exact one_sub_inverse_norm_le_one b.val
        (NeZero.ne ((poolPrimeFamily J Q Q₀).ideal b))
    · simp

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.MarkedTuples
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
lemma sum_subtype_dite_decidable {α : Type*} [Fintype α] (p : α→Prop) [DecidablePred p]
    (f : ∀ x,p x→ℂ) :
    (∑ x : {x // p x},f x.val x.property)=∑ x,if h:p x then f x h else 0 := by
  have hh := Fintype.sum_subtype_add_sum_subtype p (fun x => if h:p x then f x h else 0)
  have hz : (∑ x : {x // ¬p x},if h:p x.val then f x.val h else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dif_neg x.property
  rw [hz,add_zero] at hh
  simpa only [Subtype.property,dif_pos] using hh

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable {α : Type*} [Fintype α] (Sp : α→PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

include hR hI hF hm hf hz hbad hcop hpow hmask

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.PunctureAbsorption
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma rowResidualPart_coprime_period (I F Q : Ideal Eis) (m : Eis)
    (hQ : Q∣Ideal.span {m}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m}*F)) := by
  exact (squarefreeResidualPart_coprime (rowSimplePart I) (Ideal.span {m}*F)).symm.of_isCoprime_of_dvd_left
    (dvd_mul_of_dvd_left hQ F)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.PuncturedMarks
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma markedCompletedT_zero_punctured (Ψ : Eis→*ℂ) (m f z : Eis)
    (P : Ideal Eis) (hP : Prime P) (hm : m∈P)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) (hd : ∀ A,¬P∣A → d A=0) :
    markedCompletedT (rowTwist Ψ m f z) W X d=0 := by
  have hz (I J : Ideal Eis) : summand (rowTwist Ψ m f z) W X I J*d (I*J^3)=0 := by
    by_cases hdiv : P∣I*J^3
    · rcases hP.dvd_mul.mp hdiv with hI|hJ
      · have hz := CanonicalRowCompletion.columnWeight_zero_of_mask Ψ m f z hP hI hm
        simp only [summand,hz,zero_div,zero_mul]
      · have hz := cubeWeight_zero_of_prime_mask Ψ m f z hP (hP.dvd_of_dvd_pow hJ) hm
        simp only [summand,hz,mul_zero,zero_mul]
    · rw [hd _ hdiv,mul_zero]
  simp only [markedCompletedT,hz,tsum_zero]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.InactiveBudget
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section

lemma subtype_product_le_full {σ : Type*} [Fintype σ] (p : σ→Prop) [DecidablePred p]
    (H : σ→ℝ) (hH : ∀ i,1≤H i) :
    (∏ i : {i // p i},H i.val)≤∏ i,H i := by
  rw [←Finset.prod_subtype (Finset.univ.filter p) (by simp) H]
  exact Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
    (fun i _ => (zero_le_one.trans (hH i))) (fun i _ _ => hH i)

theorem harmonic_product_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤ rmax → (∀ i,1≤H i) →
      (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤C*(∏ i,H i)^ε := by
  let D := max 1 (256*(2+1/((ε/2)*Real.log 2)))
  have hD : 1≤D := le_max_left _ _
  refine ⟨D^(2*rmax),by positivity,?_⟩
  intro σ _ H hcard hH
  have hp : 0<∏ i,H i := Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one (hH i))
  have he (i : σ) : 256*(columnDyadicLength (H i)+1:ℝ)≤D*(H i)^(ε/2) := by
    apply (mul_le_mul_of_nonneg_left (columnDyadicLength_small_power (ε/2) (by positivity) (H i) (hH i)) (by norm_num : (0:ℝ)≤256)).trans
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (zero_le_one.trans (hH i)) _)
  calc
    _ ≤ (∏ i,D*(H i)^(ε/2))^2 := by
      apply pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => by positivity))
      exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => he i)
    _ = D^(2*Fintype.card σ)*(∏ i,H i)^ε := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        Real.finsetProd_rpow Finset.univ H (fun i _ => zero_le_one.trans (hH i)),mul_pow,←pow_mul,
        ←Real.rpow_mul_natCast hp.le]
      congr 1
      · congr 1;omega
      · congr 1;norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (Nat.mul_le_mul_left 2 hcard)) (Real.rpow_nonneg hp.le _)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.OriginalAggregation
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma bounded_row_multiplier_energy {κ : Type*} (rows : Finset κ) (r f : κ→ℂ)
    (hr : ∀ k∈rows,‖r k‖≤1) :
    (∑ k∈rows,‖r k*f k‖^2)≤∑ k∈rows,‖f k‖^2 := by
  apply Finset.sum_le_sum
  intro k hk
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hr k hk)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.SourceCost
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma pool_subset_choices_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 →
      (Fintype.card (Finset (FreeReflection.pool J Q Q₀)):ℝ)^2≤C*(Ideal.absNorm (J*Q):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := original_pool_choice_count ε hε
  refine ⟨C,hC,?_⟩
  intro J Q Q₀ hJ hQ
  apply le_trans _ (hb J Q Q₀ hJ hQ)
  simp only [Fintype.card_finset,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by norm_num) _) _

theorem original_source_cost {χ : Type*} [Fintype χ] (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤ rmax → (∀ i,1≤H i) →
    ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 →
      (Fintype.card (χ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)):ℝ)^2*
        (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤
      C*(Ideal.absNorm (J*Q):ℝ)^ε*(∏ i,H i)^ε := by
  obtain ⟨Cp,hCp,hp⟩ := pool_subset_choices_small_power ε hε
  obtain ⟨Ch,hCh,hh⟩ := harmonic_product_small_power rmax ε hε
  let C := ((Fintype.card χ:ℝ)^2+1)*(2:ℝ)^(2*rmax)*Cp*Ch
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro σ _ H hcard hH J Q Q₀ hJ hQ
  have hs : (Fintype.card (Finset σ):ℝ)^2≤(2:ℝ)^(2*rmax) := by
    simp only [Fintype.card_finset,Nat.cast_pow,Nat.cast_ofNat,←pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hcf : (Fintype.card χ:ℝ)^2≤(Fintype.card χ:ℝ)^2+1 := by linarith
  have hprod : 0≤(∏ i,H i)^ε := Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) _
  have hnp : 0≤(Ideal.absNorm (J*Q):ℝ)^ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ = (Fintype.card χ:ℝ)^2*(Fintype.card (Finset (FreeReflection.pool J Q Q₀)):ℝ)^2*
        (Fintype.card (Finset σ):ℝ)^2*(∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2 := by
      simp only [Fintype.card_prod,Nat.cast_mul,mul_pow];ring
    _ ≤ ((Fintype.card χ:ℝ)^2+1)*(Cp*(Ideal.absNorm (J*Q):ℝ)^ε)*
        (2:ℝ)^(2*rmax)*(Ch*(∏ i,H i)^ε) := by
      gcongr
      · exact hp J Q Q₀ hJ hQ
      · exact hh H hcard hH
    _ = _ := by dsimp [C];ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.SourceBudget
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem original_source_cost_budget {χ : Type*} [Fintype χ]
    (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤ rmax → (∀ i,1≤H i) →
    ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 → ∀ (Z Lpool Lslot loss : ℝ),1<Z →
      (Ideal.absNorm (J*Q):ℝ)≤Z^Lpool → (∏ i,H i)≤Z^Lslot → ε*(Lpool+Lslot)≤loss →
      (Fintype.card (χ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)):ℝ)^2*
        (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤C*Z^loss := by
  obtain ⟨C,hC,hb⟩ := original_source_cost (χ:=χ) rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ _ H hcard hH J Q Q₀ hJ hQ Z Lpool Lslot loss hZ hpool hslot hloss
  have hz : 0<Z := lt_trans zero_lt_one hZ
  apply (hb H hcard hH J Q Q₀ hJ hQ).trans
  calc
    _ ≤ C*(Z^Lpool)^ε*(Z^Lslot)^ε := by
      have hp := Real.rpow_le_rpow (Nat.cast_nonneg (Ideal.absNorm (J*Q))) hpool hε.le
      have hs := Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) hslot hε.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hs
        (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) _) (by positivity)
    _ = C*Z^(ε*(Lpool+Lslot)) := by
      rw [←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,mul_assoc,←Real.rpow_add hz]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hloss) hC.le
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.CompletedCanonicalEnergy
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

lemma maximal_prime_level_coprime (P : Ideal Eis) (hP : P.IsMaximal)
    (hg : ConcretePrimeRowBridge.goodLambda∉P) (Q₀ : Ideal Eis) (c : Eis)
    (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) (hQ : IsCoprime Q₀ P) :
    IsCoprime (Ideal.span {(9:Eis)*c}) P := by
  let S : PrimeFamily Unit := ⟨fun _ => P,fun _ => hP,fun _ => hg⟩
  exact S.level_coprime Q₀ c hc (fun _ => hQ) ()

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.LowFrozenEnergy
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_original_frozen_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (Z d ell0 shift O₀ : ℝ),
      Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) → (Ideal.absNorm J:ℝ)≤Ck*Z^(5/6-2*d) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
    Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) ((poolPrimeFamily J Q Q₀).ideal f)) →
      (∀ f,ringChar (Eis⧸(poolPrimeFamily J Q Q₀).ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J Q Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ g : γ,∀ A : Finset (FreeReflection.pool J Q Q₀),∀ T : Finset σ,
      OriginalSplitCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
        ((poolPrimeFamily J Q Q₀).restrict A) (poolPrimeFamily J Q Q₀).ideal
        rows hrows lists hmax hgood T,
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ) (scalar : γ → rows → ℂ),
      (∀ i P,‖w i P‖≤1) → (∀ g K,‖scalar g K‖≤1) →
      (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
        ∑ A : Finset (FreeReflection.pool J Q Q₀),frozenInactiveWeight J F Q Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical
            ((poolPrimeFamily J Q Q₀).restrict A) (poolPrimeFamily J Q Q₀).ideal
            rows hrows lists hmax hgood T (D g A T) (s g) (hc₀ g)
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η-O₀/2) := by
  obtain ⟨degree,C,Z₁,hC,hZ₁,he⟩ := low_original_inactive_energy a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  let ε := η/8
  have hε : 0<ε := by dsimp [ε];positivity
  obtain ⟨Cb,hCb,hcost⟩ := original_source_cost_budget (χ:=γ) rmax ε hε
  let Z₀ := max Z₁ (max 2 (max Ck (Ideal.absNorm Q:ℝ)))
  refine ⟨degree,(‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C,Z₀,by positivity,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro σ _ _ J F Q₀ hJ hF Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq hJn
    parents rows hparents hsub hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar
  have hz1 : Z₁≤Z := (le_max_left _ _).trans hZ
  have hz : 1<Z := lt_of_lt_of_le hZ₁ hz1
  have hzp : 0<Z := lt_trans zero_lt_one hz
  let FF := (poolPrimeFamily J Q Q₀).ideal
  have hall := fun (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) =>
    he g J F Q₀ hJ hF A Z d ell0 shift O₀
      hz1 hd hd1 hell hellcap hshift hOeq
      parents rows hparents hsub hbad lists H hdis hmax hgood hprime hrows hH1 hH hprod
      (fun f => hGN f.val) (fun f => hGchar f.val)
      (fun K hK => ⟨fun f => (hrowcop K hK).1 f.val,(hrowcop K hK).2⟩) hLN hLchar T
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ w scalar hw hscalar
  let energy := C*(1+‖θ‖)^degree*Z^((5/6-2*d)+505*η-O₀/2)
  let harm := (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2
  let source := fun (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) (K : rows) =>
    originalInactivePhysical ((poolPrimeFamily J Q Q₀).restrict A) FF rows hrows lists hmax hgood T
      (D g A T) (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K
  have hs (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) :
      (∑ K : rows,‖source g A T K‖^2)≤harm*energy := by
    apply (hD g A T θ w hw).trans
    apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact subtype_product_le_full (fun i => i∉T) (fun i => 256*(columnDyadicLength (H i)+1:ℝ)) (fun i => by have hn : (0:ℝ)≤ columnDyadicLength (H i) := Nat.cast_nonneg _; linarith)
  let Labels := γ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)
  let f := fun (b : Labels) (K : rows) => (scalar b.1 K*frozenInactiveWeight J F Q Q₀ b.2.1)*source b.1 b.2.1 b.2.2 K
  have hf (b : Labels) : (∑ K : rows,‖f b K‖^2)≤harm*energy := by
    apply (bounded_row_multiplier_energy Finset.univ _ _ (fun K hK => ?_)).trans (hs b.1 b.2.1 b.2.2)
    rw [norm_mul]
    exact (mul_le_mul (hscalar b.1 K) (frozenInactiveWeight_norm J F Q Q₀ b.2.1)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hfam := weighted_finite_row_energy_uniform (Finset.univ : Finset Labels) (Finset.univ : Finset rows)
    (fun _ => (1:ℂ)) f (harm*energy) (fun b _ => hf b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hfam
  have hid (K : rows) : (∑ b : Labels,f b K)=∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J Q Q₀),frozenInactiveWeight J F Q Q₀ A*
        ∑ T : Finset σ,source g A T K := by
    simp only [Labels,f,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  have hsource : (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J Q Q₀),frozenInactiveWeight J F Q Q₀ A*
        ∑ T : Finset σ,source g A T K‖^2)≤
      ‖thetaDerivativeScalar⁻¹‖^2*(Fintype.card Labels:ℝ)^2*harm*energy := by
    simp_rw [←hid]
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hfam (sq_nonneg _)).trans_eq (by ring)
  apply hsource.trans
  have hQn : (Ideal.absNorm Q:ℝ)≤Z := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hCkZ : Ck≤Z := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hJcap : (Ideal.absNorm J:ℝ)≤Z^(2:ℝ) := by
    apply hJn.trans
    calc
      Ck*Z^(5/6-2*d) ≤ Z*Z^(5/6-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzp.le _)
      _ = Z^(1+(5/6-2*d)) := by rw [Real.rpow_add hzp,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
  have hpool : (Ideal.absNorm (J*Q):ℝ)≤Z^(3:ℝ) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ Z^(2:ℝ)*Z := mul_le_mul hJcap hQn (Nat.cast_nonneg _) (Real.rpow_nonneg hzp.le _)
      _ = _ := by norm_num;ring
  have hslot : (∏ i,H i)≤Z^(2:ℝ) := hprod.trans
    (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith))
  have hcst := hcost H hcard hH1 J Q Q₀ hJ hQ Z 3 2 η hz hpool hslot (by dsimp [ε];linarith)
  calc
    _ = ‖thetaDerivativeScalar⁻¹‖^2*((Fintype.card Labels:ℝ)^2*harm)*energy := by ring
    _ ≤ (‖thetaDerivativeScalar⁻¹‖^2+1)*(Cb*Z^(η))*energy := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
      exact mul_le_mul (by linarith) hcst (by dsimp [harm];positivity) (by positivity)
    _ = ((‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C)*(1+‖θ‖)^degree*
        Z^(η+((5/6-2*d)+505*η-O₀/2)) := by
      dsimp only [energy]
      rw [Real.rpow_add hzp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.LowCompletedFiber
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_completed_fiber_energy (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J : Ideal Eis) (_hJ : J≠0)
      (Z d ell0 shift : ℝ), Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
      (Ideal.absNorm J:ℝ)≤Ck*Z^(5/6-2*d) →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈representativeRowFiber parents J (Ideal.span {m}*F),
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
  let Q₀ := Q*Ideal.span {(72:Eis)}
  let c : Eis := (9:Eis)*(ConcretePrimeRowBridge.idealGenerator Q)*(72:Eis)
  have hc : c≠0 := mul_ne_zero (mul_ne_zero (by norm_num)
    (ConcretePrimeRowBridge.idealGenerator_ne_zero Q hQ)) (by norm_num)
  have hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀ := by
    dsimp only [c,Q₀]
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      ConcretePrimeRowBridge.span_idealGenerator]
    ring
  let : Finite (Eis⧸Ideal.span {c}) := ConcreteTraceCRT.finite_quotient_span hc
  let : Fintype (Eis⧸Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (Eis⧸Ideal.span {((9:Eis)*c)^2}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (mul_ne_zero (by norm_num) hc))
  let : Fintype (Eis⧸Ideal.span {((9:Eis)*c)^2}) := Fintype.ofFinite _
  let mask := Ideal.span {m}*F
  have hmask0 : mask≠0 := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  let E := fixedFourierGeometry c hc
  have hEc : ∀ h,(E h).c0≠0 := fun h => (E h).denominator_ne_zero
  have hEN : ∀ h,(9:Eis)*(E h).c0∣(9:Eis)*c := fun h => mul_dvd_mul_left (9:Eis) (E h).denominator_dvd
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_original_frozen_energy
    (fun h => (E h).a0) (fun h => (E h).c0) (fun h => (E h).mode) lo hi hlo W hWs hW
    (fun h => (E h).shape) hEc hEN (fun h => (E h).primary) (fun h => (E h).coprime)
    mask hmask0 Ck η hCk hη hη1 rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J hJ Z d ell0 shift hZ hd hd1 hell hellcap hshift hJn
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let rows := originalResidualRows parents J mask
  have hparents0 : ∀ I∈parents,I≠0 := fun I hI => (hparents I hI).1
  let hrows : ∀ K∈rows,Admissible K := originalResidualAdmissible parents J F m hbad
  have hcop : ∀ K∈rows,IsCoprime Q₀ K := by
    intro K hK
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    exact rowResidualPart_coprime_period I F Q₀ m hperiod
  have hGN : ∀ f,IsCoprime (Ideal.span {(9:Eis)*c}) ((poolPrimeFamily J mask Q₀).ideal f) :=
    (poolPrimeFamily J mask Q₀).level_coprime Q₀ c hcQ (poolPrimeFamily_period J mask Q₀)
  have hrowcop : ∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J mask Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {(9:Eis)*c}) K := by
    intro K hK
    refine ⟨?_,residual_level_coprime K Q₀ (hrows K hK) c hcQ (hcop K hK)⟩
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨hIp,hpow,hmask'⟩ := Finset.mem_filter.mp hI
    exact poolPrimeFamily_fiber_row_coprime J I mask Q₀ hJ (hparents0 I hIp) hmask0 hpow.symm hmask'.symm
  have hLN : ∀ i,∀ P∈lists i,IsCoprime (Ideal.span {(9:Eis)*c}) P :=
    fun i P hP => maximal_prime_level_coprime P (hmax i P hP) (hgood i P hP) Q₀ c hcQ (hLP i P hP)
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0<Z := lt_trans zero_lt_one hz
  let O := normWidth Z (rowPowerfulPart J)
  have hO : 0≤O := normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero J)
  have hPowPos : 0<(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
    have := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
    linarith
  obtain ⟨D,hD⟩ := he (σ:=σ) J F Q₀ hJ hF.ne_zero Z d ell0 shift O
    hZ hd hd1 hell hellcap hshift rfl hJn parents rows hparents (Finset.Subset.refl _) hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN (poolPrimeFamily_odd J mask Q₀)
    hrowcop hLN hodd
  let scalar := fun h (K : rows) => fixedThetaRowCoeff c hc
    ((residualOriginalData parents J F hF m hm hparents0 u K).fixedFactor Ψ Q) h
  have hscalar : ∀ h K,‖scalar h K‖≤1 := fun h K =>
    (residualOriginalData parents J F hF m hm hparents0 u K).fixedCoefficient_norm Ψ Q hΨnorm c hc h
  have henergy := hD θ w scalar hw hscalar
  have hTw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) :=
    CanonicalRowCompletion.normTwistedSource_contDiff W lo hi hlo hWs hW θ
  have hTs := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hTc : HasCompactSupport (CompletedHeight.normTwistedSource W θ) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by
      by_contra hn
      exact hx (hTs hn))
  have hid (K : rows) := original_completed_residual_source parents J F hJ hF m hm hparents0 u hbad
    Q hQ c hc hcQ E hcop lists hmax hgood hdis hodd hLP D Ψ hΨnorm hΨperiod hmLam hm2
    (CompletedHeight.normTwistedSource W θ) hTc lo hi hlo hTs hTw (Z^(1+ell0+shift)) (Real.rpow_pos_of_pos hzp _) w K
  have hre := original_fiber_energy_reindex parents J (mask) hparents0
    (fun I => ∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))
  rw [hre]
  have heq : (∑ K : rows,‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K.val)))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)=
      ∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ h,scalar h K*
        ∑ A : Finset (FreeReflection.pool J mask Q₀),frozenInactiveWeight J F mask Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical ((poolPrimeFamily J mask Q₀).restrict A)
            (poolPrimeFamily J mask Q₀).ideal rows hrows lists hmax hgood T (D h A T) (E h).shape (E h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hid K)
  have hbound := heq.trans_le henergy
  have hp : Z^O=(Ideal.absNorm (rowPowerfulPart J):ℝ) := Real.rpow_logb hzp (ne_of_gt hz) hPowPos
  have hR : C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η-O/2)=
      C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
    rw [show (5/6-2*d)+506*η-O/2=((5/6-2*d)+506*η)+O*(-(1/2:ℝ)) by ring,
      Real.rpow_add hzp,Real.rpow_mul hzp.le,hp]
    ring
  have hs := Finset.sum_coe_sort rows (fun K : Ideal Eis =>
    ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K)))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
  exact hs.symm.trans_le (hbound.trans_eq hR)
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.LowCompletedRows
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_completed_rows_energy (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((5/6-2*d)+507*η) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_completed_fiber_energy Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck η hCk hη hη1 rmax
  obtain ⟨D,hD,ha⟩ := completed_representative_aggregation 2 η (by norm_num) hη
  let mask := Ideal.span {m}*F
  let Z₁ := max Z₀ (max 2 (max Ck (Ideal.absNorm mask:ℝ)))
  refine ⟨degree,D*C,Z₁,mul_pos hD hC,lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ _ Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  have hZZ : Z₀≤Z := (le_max_left _ _).trans hZ
  have hZ2 : 2≤Z := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hCkZ : Ck≤Z := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskZ : (Ideal.absNorm mask:ℝ)≤Z := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskn : (Ideal.absNorm mask:ℝ)≤Z^(2:ℝ) := hmaskZ.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hz1 (show (1:ℝ)≤2 by norm_num))
  have hparentn : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(2:ℝ) := by
    intro I hI
    refine ⟨(hparents I hI).1,(hparents I hI).2.trans ?_⟩
    calc
      _ ≤ Z*Z^(5/6-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+(5/6-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  have hh := ha Z hZ2 parents mask hparentn
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hmaskn
    (C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η))
    (fun I => ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
      (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
    (by positivity) (fun J hJ => he (σ:=σ) J (hparents J hJ).1 Z d ell0 shift
      hZZ hd hd1 hell hellcap hshift (hparents J hJ).2
      parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod
      Ψ hΨnorm hΨperiod u θ w hw)
  apply hh.trans_eq
  calc
    _ = (D*C)*(1+‖θ‖)^degree*(Z^η*Z^((5/6-2*d)+506*η)) := by ring
    _ = _ := by rw [←Real.rpow_add hz]; congr 2; ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.PunctureLists
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma sum_puncture_lists (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis))
    (f : (∀ i,lists i)→ℂ) (hz : ∀ p,(∃ i,(p i).val∈S) → f p=0) :
    (∑ p : ∀ i,lists i,f p)=∑ p : ∀ i,punctureLists lists S i,f (punctureListLift lists S p) := by
  have he := (punctureListEquiv lists S).sum_comp (fun p => f p.val)
  have hs := sum_subtype_dite_decidable (fun p : ∀ i,lists i => ∀ i,(p i).val∉S) (fun p _ => f p)
  calc
    _ = ∑ p : ∀ i,lists i,if h:∀ i,(p i).val∉S then f p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs with h
      · rfl
      · exact hz p (by simpa only [not_forall,not_not] using h)
    _ = ∑ p : {p : ∀ i,lists i // ∀ i,(p i).val∉S},f p.val := hs.symm
    _ = _ := he.symm

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.LowPunctureLists
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
lemma actualPuncturePrimes_mem (lists : σ→Finset (Ideal Eis)) (m : Eis)
    (i : σ) (P : Ideal Eis) (hP : P∈lists i) :
    P∈actualPuncturePrimes lists m ↔ m∈P := by
  simp only [actualPuncturePrimes,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hP⟩)

lemma puncture_period_coprime (Q : Ideal Eis) (m : Eis) (hQ : Q∣Ideal.span {m})
    (P : Ideal Eis) (hP : P.IsMaximal) (hm : m∉P) : IsCoprime Q P := by
  let : P.IsMaximal := hP
  have hp : ¬P∣Ideal.span {m} := by
    intro h
    exact hm ((Ideal.dvd_iff_le.mp h) (Ideal.subset_span (Set.mem_singleton m)))
  exact (maximal_coprime_of_not_dvd P (Ideal.span {m}) hp).symm.of_isCoprime_of_dvd_left hQ

theorem original_completed_actual_puncture_lists (lists : σ→Finset (Ideal Eis))
    (hprime : ∀ i,∀ P∈lists i,Prime P)
    (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists (actualPuncturePrimes lists m) i,
      (∏ i,w i (punctureListLift lists (actualPuncturePrimes lists m) p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists (actualPuncturePrimes lists m)
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m∈(p i).val := (Finset.mem_filter.mp hi).2
  have hz := markedCompletedT_zero_punctured Ψ m f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hA))
  exact mul_eq_zero_of_right _ hz
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.LowOriginalEnergy
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_original_completed_energy_oai (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((5/6-2*d)+507*η) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_completed_rows_energy Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck η hCk hη hη1 rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let S := actualPuncturePrimes lists m
  let lists' := punctureLists lists S
  have hsub (i : σ) : lists' i⊆lists i := Finset.filter_subset _ _
  let w' : ∀ i,lists' i→ℂ := fun i P => w i ⟨P.val,hsub i P.property⟩
  have hLP (i : σ) (P : Ideal Eis) (hP : P∈lists' i) : IsCoprime (Q*Ideal.span {(72:Eis)}) P := by
    apply puncture_period_coprime _ m hperiod P (hmax i P (hsub i hP))
    intro hmP
    exact (Finset.mem_filter.mp hP).2 ((actualPuncturePrimes_mem lists m i P (hsub i hP)).mpr hmP)
  have hh := he (σ:=σ) Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists' H
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j))
    (fun i P hP => hmax i P (hsub i hP)) (fun i P hP => hgood i P (hsub i hP))
    (fun i P hP => hprime i P (hsub i hP)) (fun i P hP => hodd i P (hsub i hP))
    hLP hH1 (fun i P hP => hH i P (hsub i hP)) hprod
    Ψ hΨnorm hΨperiod u θ w' (fun i P => hw i ⟨P.val,hsub i P.property⟩)
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro I hI
  exact congrArg (fun z : ℂ => ‖z‖^2) (original_completed_actual_puncture_lists lists hprime Ψ m
    (ConcretePrimeRowBridge.idealGenerator F) (u.val*ConcretePrimeRowBridge.idealGenerator I)
    (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w)
end
end SevenEighths.InverseReflectedPhase

end OAI
end

theorem solution.{v} : type_of% @OAI.SevenEighths.InverseReflectedPhase.low_original_completed_energy_oai.{v} := @OAI.SevenEighths.InverseReflectedPhase.low_original_completed_energy_oai.{v}
