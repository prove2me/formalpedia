-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.HasSieveExponent.lifted_annular_selected
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T00:51:05.321466+00:00
-- url     : https://prove2.me/submissions/713d26c6-61ab-4295-a4f5-7b8a31c0a372

import Mathlib
import Definitions.Def_OAIHecke78B008
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_annular_selected_bound

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConstantDirichletSeries
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

open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction

theorem coefficientAtScale_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell X X (coefficientAtScale N X a) := by
  intro J hJ
  unfold coefficientAtScale at hJ
  split_ifs at hJ with h
  · exact ha ⟨J.val, h⟩ hJ
  · exact (hJ rfl).elim

theorem coefficientAtScale_row_sum (N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) (z : O) :
    (∑ J : idealRange N, quadraticRow J.val z * a J) =
      ∑ J : idealRange X, quadraticRow J.val z * coefficientAtScale N X a J := by
  let f : Ideal O → ℂ := fun I => if h : I ∈ idealRange N then quadraticRow I z * a ⟨I, h⟩ else 0
  have hleft : (∑ J : idealRange N, quadraticRow J.val z * a J) = ∑ I ∈ idealRange N, f I := by
    rw [← Finset.sum_coe_sort (idealRange N) f]
    apply Finset.sum_congr rfl
    intro J _
    simp only [f, dif_pos J.property]
  have hright : (∑ J : idealRange X, quadraticRow J.val z * coefficientAtScale N X a J) =
      ∑ I ∈ idealRange X, f I := by
    rw [← Finset.sum_coe_sort (idealRange X) f]
    apply Finset.sum_congr rfl
    intro J _
    unfold coefficientAtScale
    split_ifs with h <;> simp only [f, h, ↓reduceDIte, mul_zero]
  rw [hleft, hright]
  rcases le_total N X with hNX | hXN
  · apply Finset.sum_subset (idealRange_mono hNX)
    intro I hIX hIN
    simp only [f, dif_neg hIN]
  · symm
    apply Finset.sum_subset (idealRange_mono hXN)
    intro I hIN hIX
    have haI : a ⟨I, hIN⟩ = 0 := by
      by_contra hn
      exact hIX (mem_idealRange.mpr ⟨(mem_idealRange.mp hIN).1, ha ⟨I, hIN⟩ hn⟩)
    simp only [f, dif_pos hIN, haI, mul_zero]

theorem coefficientAtScale_energy (N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) :
    (∑ J : idealRange N, ‖a J‖ ^ 2) = ∑ J : idealRange X, ‖coefficientAtScale N X a J‖ ^ 2 := by
  let f : Ideal O → ℝ := fun I => if h : I ∈ idealRange N then ‖a ⟨I, h⟩‖ ^ 2 else 0
  have hleft : (∑ J : idealRange N, ‖a J‖ ^ 2) = ∑ I ∈ idealRange N, f I := by
    rw [← Finset.sum_coe_sort (idealRange N) f]
    apply Finset.sum_congr rfl
    intro J _
    simp only [f, dif_pos J.property]
  have hright : (∑ J : idealRange X, ‖coefficientAtScale N X a J‖ ^ 2) =
      ∑ I ∈ idealRange X, f I := by
    rw [← Finset.sum_coe_sort (idealRange X) f]
    apply Finset.sum_congr rfl
    intro J _
    unfold coefficientAtScale
    split_ifs with h <;> simp only [f, h, ↓reduceDIte, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [hleft, hright]
  rcases le_total N X with hNX | hXN
  · apply Finset.sum_subset (idealRange_mono hNX)
    intro I hIX hIN
    simp only [f, dif_neg hIN]
  · symm
    apply Finset.sum_subset (idealRange_mono hXN)
    intro I hIN hIX
    have haI : a ⟨I, hIN⟩ = 0 := by
      by_contra hn
      exact hIX (mem_idealRange.mpr ⟨(mem_idealRange.mp hIN).1, ha ⟨I, hIN⟩ hn⟩)
    simp only [f, dif_pos hIN, haI, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem annularHighEnergy_coefficientAtScale (M N X K : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) :
    annularHighEnergy M N K a = annularHighEnergy M X K (coefficientAtScale N X a) := by
  unfold annularHighEnergy
  simp_rw [coefficientAtScale_row_sum N X a ha]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularLifting
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

theorem cutoffRescaleCoefficient_eq (C η r q : ℝ) (hr : 0< r) (hq : 0<q) :
    cutoffRescaleCoefficient C η r q=C*r^(1-η)*q^(2+η) := by
  rw [cutoffRescaleCoefficient,Real.div_rpow hr.le hq.le,
    Real.rpow_sub hr,Real.rpow_one,Real.rpow_add hq,Real.rpow_two]
  have hrp : r^η≠0 := (Real.rpow_pos_of_pos hr η).ne'
  have hqp : q^η≠0 := (Real.rpow_pos_of_pos hq η).ne'
  field_simp

theorem cutoffRescaleCoefficient_bounds (C η r q : ℝ)
    (hC : 0≤C) (hη : 0≤η) (hη1 : η≤1) (hr : 1≤ r) (hr64 : r≤64) (hq : 1≤q) (hq7 : q≤7) :
    C≤ cutoffRescaleCoefficient C η r q ∧ cutoffRescaleCoefficient C η r q≤21952*C := by
  rw [cutoffRescaleCoefficient_eq C η r q (by linarith) (by linarith)]
  have hrlo : 1≤ r^(1-η) := Real.one_le_rpow hr (by linarith)
  have hqlo : 1≤q^(2+η) := Real.one_le_rpow hq (by linarith)
  have hrup : r^(1-η)≤ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr (show 1-η≤1 by linarith)
  have hqup : q^(2+η)≤q^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hq (show 2+η≤(3:ℝ) by linarith)
  constructor
  · calc
      C = C*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ C*r*q^3 := by gcongr
      _ ≤ C*64*7^3 := by gcongr
      _ = _ := by ring

theorem selectedPoissonK_rescale (C M X η r q : ℝ)
    (hM : 0<M) (hX : 0<X) (hr : 0< r) (hq : 0<q) :
    selectedPoissonK (cutoffRescaleCoefficient C η r q) (r*M) (X/q) η =
      selectedPoissonK C M X η := by
  unfold selectedPoissonK selectedPoissonT cutoffRescaleCoefficient
  have he : (r*M)*(X/q)=(r/q)*(M*X) := by ring
  rw [he,Real.mul_rpow (by positivity : 0≤ r/q) (by positivity : 0≤M*X)]
  have hp : (r/q)^η≠0 := (Real.rpow_pos_of_pos (by positivity) η).ne'
  field_simp

end

open scoped BigOperators Classical

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents
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

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

namespace CanonicalQuadraticSieve

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

theorem fixedCutoffBase_bounds : 4≤fixedCutoffBase ∧ fixedBadNorm≤fixedCutoffBase :=
  ⟨le_max_left _ _,le_max_right _ _⟩

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicLoss
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

theorem lifting_annular_scale_bounds (j : Fin 7) : 1≤(2:ℝ)^j.val ∧ (2:ℝ)^j.val≤64 := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  have hj : j.val≤6 := by omega
  have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj
  norm_num at hh
  exact hh

theorem HasSieveExponent.lifted_annular_selected_oai {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤ selectedPoissonK fixedCutoffBase M N η →
      ∀ (j : Fin 7) (q : ℝ), 1≤q → q≤7 →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N (N/q) a →
      annularHighEnergy ((2:ℝ)^j.val*M) N (selectedPoissonK fixedCutoffBase M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hc0 : 0<fixedCutoffBase := lt_of_lt_of_le (by norm_num) fixedCutoffBase_bounds.1
  obtain ⟨C,hC,hann⟩ := hexp.annular_selected_bound hα1 hα2 η hη hη1 l A hl hA
    (21952*fixedCutoffBase) (by linarith [fixedCutoffBase_bounds.1])
  refine ⟨C*64^(260*η)*64,by positivity,?_⟩
  intro M N hM hN hthreshold hK j q hq hq7 a ha
  let r : ℝ := (2:ℝ)^j.val
  have hr := lifting_annular_scale_bounds j
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hq0 : 0<q := by linarith
  have hr0 : 0< r := by dsimp [r]; positivity
  have hNq : 4≤N/q := (le_div_iff₀ hq0).mpr (by nlinarith)
  have hNqN : N/q≤N := div_le_self hN0.le hq
  have hβ : 0≤2-1/α := by
    have hfrac : 1/α≤1 := (div_le_one (by linarith : 0<α)).mpr hα1
    linarith
  have hth : (N/q)^(2-1/α)≤ r*M := by
    calc
      _ ≤ N^(2-1/α) := Real.rpow_le_rpow (by positivity) hNqN hβ
      _ ≤ M := hthreshold
      _ ≤ r*M := by nlinarith [hr.1]
  let c := cutoffRescaleCoefficient fixedCutoffBase η r q
  have hc := cutoffRescaleCoefficient_bounds fixedCutoffBase η r q hc0.le hη.le hη1 hr.1 hr.2 hq hq7
  have hk := selectedPoissonK_rescale fixedCutoffBase M N η r q hM0 hN0 hr0 hq0
  have hh := hann c (r*M) (N/q) hc.1 hc.2 (by nlinarith [hr.1]) hNq hth
    (by simpa only [c,hk] using hK) (coefficientAtScale N (N/q) a)
    (coefficientAtScale_shell N (N/q) a ha)
  dsimp only [c] at hh
  rw [hk,←annularHighEnergy_coefficientAtScale (r*M) N (N/q)
    (selectedPoissonK fixedCutoffBase M N η) a (fun J hJ => (ha J hJ).2),
    ←coefficientAtScale_energy N (N/q) a (fun J hJ => (ha J hJ).2)] at hh
  have hp : ((r*M)*(N/q))^(260*η)≤64^(260*η)*(M*N)^(260*η) := by
    calc
      _ ≤ (64*(M*N))^(260*η) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        calc
          (r*M)*(N/q) ≤ (64*M)*N := by gcongr; exact hr.2
          _ = _ := by ring
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  change annularHighEnergy (r*M) N _ a≤_
  apply hh.trans
  calc
    _ ≤ C*(64^(260*η)*(M*N)^(260*η))*(64*M)*∑J,‖a J‖^2 := by
      gcongr
      exact hr.2
    _ = _ := by ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical

end

end OAI
end

theorem solution : type_of% @OAI.CanonicalQuadraticSieve.HasSieveExponent.lifted_annular_selected_oai := @OAI.CanonicalQuadraticSieve.HasSieveExponent.lifted_annular_selected_oai
