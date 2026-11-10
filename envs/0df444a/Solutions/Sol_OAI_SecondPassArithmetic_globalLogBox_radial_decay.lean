-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalLogBox_radial_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:46:59.003848+00:00
-- url     : https://prove2.me/submissions/860c06e1-a1c9-473a-9807-a29238a694e0

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogBox_total_loss
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinLossScale_nonneg

set_option autoImplicit false
open OAI
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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
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
open OAI.SecondPassArithmetic
namespace OAI.SecondPassArithmetic
theorem _root_.solution (ε : ℝ) (hε : 0<ε) (η : ℝ) (hη : 0≤η) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U Z θ : ℝ, ∀ N : ℕ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z →
      (∑j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        (globalBinLossScale B j)^η/
          (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N) ≤
        C*U^(ε+8*η)/Z^(θ*N) := by
  obtain ⟨C,hC,hall⟩ := globalLogBox_total_loss ε hε η hη
  refine ⟨C,hC,?_⟩
  intro K ell B F M H U Z θ N hU hK hell hB hF hH hKU hellU hBU hHU heU hZ
  let box := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let radial := fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j
  have hbase : 0<Z^θ := Real.rpow_pos_of_pos hZ _
  have hden : 0<Z^(θ*N) := Real.rpow_pos_of_pos hZ _
  have hnum (j : GlobalLogIndex) : 0≤(globalBinLossScale B j)^η :=
    Real.rpow_nonneg (globalBinLossScale_nonneg B (by linarith) j) _
  have hp (j : GlobalLogIndex) (hj : Z^θ≤radial j) :
      Z^(θ*N)≤(1+radial j)^N := by
    rw [Real.rpow_mul hZ.le,Real.rpow_natCast]
    exact pow_le_pow_left₀ hbase.le (by linarith) N
  calc
    _ ≤ ∑j∈box.filter (fun j => Z^θ≤radial j), (globalBinLossScale B j)^η/Z^(θ*N) := by
      apply Finset.sum_le_sum
      intro j hj
      exact div_le_div_of_nonneg_left (hnum j) hden (hp j (Finset.mem_filter.mp hj).2)
    _ = (∑j∈box.filter (fun j => Z^θ≤radial j),(globalBinLossScale B j)^η)/Z^(θ*N) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ (∑j∈box,(globalBinLossScale B j)^η)/Z^(θ*N) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => hnum j)
    _ ≤ C*U^(ε+8*η)/Z^(θ*N) := div_le_div_of_nonneg_right
      (hall K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) hden.le
end OAI.SecondPassArithmetic
