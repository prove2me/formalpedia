-- Prove2me | solution 1 for OAI.SecondPassArithmetic.idealChildRow_energy_le_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:48:31.099381+00:00
-- url     : https://prove2.me/submissions/2b033c2f-1fb7-414a-930a-c62ca66da860

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_SupportBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningSeparation
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogSeparation
import Theorems.Thm_OAI_SecondPassArithmetic_childLabelRotation_injective
import Theorems.Thm_OAI_SecondPassArithmetic_childLabelRotation_norm
import Theorems.Thm_OAI_SecondPassArithmetic_childLabelRotation_ne_zero
import Theorems.Thm_OAI_SecondPassArithmetic_idealChildRow_eq_rotated
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span
import Theorems.Thm_OAI_SecondPassArithmetic_finite_nonzero_row_energy_le_majorant
import Theorems.Thm_OAI_SecondPassArithmetic_mem_firstFrequencyDisk


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels
variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (negative : Bool) (u : ActualEisensteinCubic.Oˣ)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ) (hK : 0<K)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    (∑z∈T,‖idealChildRow p hp hcop hg pool Ψ m H negative u z‖^2)≤
      canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K := by
  let f : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O → ℝ := fun z=>
    ‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator z.1) z.2‖^2
  let R := (firstFrequencyDisk K).erase 0
  have hsub : T.image (childLabelRotation u negative)⊆labels.product R := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_product.mpr
    refine ⟨hlabels z hz,Finset.mem_erase.mpr ⟨childLabelRotation_ne_zero u negative z (hzero z hz),?_⟩⟩
    apply (mem_firstFrequencyDisk K _).mpr
    rw [childLabelRotation_norm]
    exact hrows z hz
  calc
    _ = ∑w∈T.image (childLabelRotation u negative),f w := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro z hz
        rw [idealChildRow_eq_rotated]
      · exact fun _ _ _ _ he=>childLabelRotation_injective u negative he
    _ ≤ ∑w∈labels.product R,f w :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>sq_nonneg _)
    _ = ∑I∈labels,∑z∈R,f (I,z) := by rw [Finset.product_eq_sprod,Finset.sum_product]
    _ ≤ ∑I∈labels,(nonzeroRowMajorantSum
        (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) K).re := by
      apply Finset.sum_le_sum
      intro I hI
      apply finite_nonzero_row_energy_le_majorant _ R K hK
      · intro z hz
        rw [←eisEmbedding_norm_sq_eq_absNorm_span]
        exact (mem_firstFrequencyDisk K z).mp (Finset.mem_erase.mp hz).2
      · exact fun z hz=>(Finset.mem_erase.mp hz).1
    _ = _ := by unfold canonicalSmoothedEnergy; rw [Complex.re_sum]
end OAI.SecondPassArithmetic
