-- Prove2me | solution 1 for OAI.CubicEisenstein.cusp_hardy_halfline_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T20:01:32.489322+00:00
-- url     : https://prove2.me/submissions/a535a587-2b6f-453c-b16d-9ec07fb81856

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Theorems.Thm_OAI_CubicEisenstein_cusp_hardy_interval_lintegral

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (f : ℝ → ℂ) (a : ℝ) (ha : 0<a) (hfa : f a=0)
    (hf : ∀t∈Set.Ici a,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Ici a)) :
    (∫⁻t in Set.Ioi a,ENNReal.ofReal (‖f t‖^2/t^3))≤
      ∫⁻t in Set.Ioi a,ENNReal.ofReal (‖deriv f t‖^2/t) := by
  have hcover : (⋃n : ℕ,Set.Ioc a (a+n))=Set.Ioi a := by
    ext t
    constructor
    · rintro ⟨_,⟨n,rfl⟩,ht⟩
      exact ht.1
    · intro ht
      obtain ⟨n,hn⟩ := exists_nat_ge (t-a)
      exact Set.mem_iUnion.mpr ⟨n,ht,by linarith⟩
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Set.Ioc a (a+n)) := by
    intro m n
    refine ⟨max m n,Set.Ioc_subset_Ioc_right ?_,Set.Ioc_subset_Ioc_right ?_⟩
    · change a+(m:ℝ)≤a+((max m n:ℕ):ℝ)
      have hh : (m:ℝ)≤((max m n:ℕ):ℝ) := by exact_mod_cast le_max_left m n
      linarith
    · change a+(n:ℝ)≤a+((max m n:ℕ):ℝ)
      have hh : (n:ℝ)≤((max m n:ℕ):ℝ) := by exact_mod_cast le_max_right m n
      linarith
  calc
    _ = ⨆n : ℕ,∫⁻t in Set.Ioc a (a+n),ENNReal.ofReal (‖f t‖^2/t^3) := by
      rw [←hcover]
      exact setLIntegral_iUnion_of_directed _ hdir
    _ ≤ _ := by
      apply iSup_le
      intro n
      exact (cusp_hardy_interval_lintegral f a (a+n) ha (le_add_of_nonneg_right (Nat.cast_nonneg n)) hfa
        (fun t ht => hf t ht.1) (hdf.mono (fun t ht => ht.1))).trans
          (lintegral_mono_set Set.Ioc_subset_Ioi_self)
end OAI.CubicEisenstein
