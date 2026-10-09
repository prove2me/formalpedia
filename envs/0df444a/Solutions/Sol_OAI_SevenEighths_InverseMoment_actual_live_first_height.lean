-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.actual_live_first_height
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:55:26.499272+00:00
-- url     : https://prove2.me/submissions/8c725112-86af-4a2c-89d2-9413d0d33889

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Theorems.Thm_OAI_SevenEighths_InverseMoment_global_priority_filtered_physical_step_uniform_types
import Theorems.Thm_OAI_SevenEighths_InverseMoment_original_live_step_scalars
import Theorems.Thm_OAI_SevenEighths_InverseMomentFirstLabelCell_source_step_arithmetic

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase
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

namespace ActualEisensteinCubic

theorem finiteSquarefreeRow_sixth_power
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSquarefreeRow P hgood S (a ^ 6) =
      if ∃ i ∈ S, a ∈ P i then 0 else 1 := by
  classical
  simp only [finiteSquarefreeRow]
  by_cases hex : ∃ i ∈ S, a ∈ P i
  · obtain ⟨i, hi, hai⟩ := hex
    rw [if_pos ⟨i, hi, hai⟩]
    apply Finset.prod_eq_zero hi
    rw [canonicalSextic_sixth_power_mask]
    simp [hai]
  · rw [if_neg hex]
    apply Finset.prod_eq_one
    intro i hi
    rw [canonicalSextic_sixth_power_mask]
    simp [show a ∉ P i by intro hai; exact hex ⟨i, hi, hai⟩]

end ActualEisensteinCubic

end

end OAI
end

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

theorem squarefreeGaussCoefficient_eq (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    squarefreeGaussCoefficient I =
      star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I hI := by
  rw [squarefreeGaussCoefficient, dif_pos ⟨hs, hI⟩]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
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

open ActualEisensteinCubic

open ActualEisensteinCubic ConcreteTraceCRT

theorem product_primary {ι : Type*} [Fintype ι] (p : ι → O)
    (hp : ∀ i, lambda ^ 2 ∣ p i - 1) : lambda ^ 2 ∣ (∏ i, p i) - 1 := by
  apply primary_multiset_prod (Finset.univ.val.map p)
  intro r hr
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hr
  exact hp i

theorem cubicRow_product_mk {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) (a : O) :
    cubicRow (Ideal.span {∏ i, p i}) hI (Ideal.Quotient.mk (Ideal.span {∏ i, p i}) a) =
      ∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (Ideal.Quotient.mk (Ideal.span {p i}) a) := by
  rw [cubicRow_mk]
  symm
  exact (productPrimeIndexEquiv p hcop).prod_comp (fun P =>
    (canonicalSextic P.val (primeIndex_good _ hI P) ^ 2) (Ideal.Quotient.mk P.val a))

theorem gaussTwo_eq_canonicalProductGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) :
    gaussTwo (Ideal.span {∏ i, p i}) hI =
      FiniteGaussPhase.canonicalProductGauss p hp hcop hgood (fun _ => 2) := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  let : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  let : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := finite_quotient_span hI
  let : Fintype (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec (Ideal.span {∏ i, p i}) hI).1
  have hsum :
      (∑ x : O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})},
        cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (primaryGenerator (Ideal.span {∏ i, p i})) hI x) =
      (∑ x : O ⧸ Ideal.span {∏ i, p i},
        (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
          (FiniteGaussPhase.productElementCRT p hcop x i)) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (∏ i, p i) hpall x) := by
    apply Fintype.sum_equiv e.toEquiv
    intro x
    change cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (primaryGenerator (Ideal.span {∏ i, p i})) hI x =
      (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (FiniteGaussPhase.productElementCRT p hcop (e x) i)) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (∏ i, p i) hpall (e x)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [e, Ideal.quotEquivOfEq_mk, cubicRow_product_mk p hcop hgood hI,
      FiniteGaussPhase.productElementCRT_mk, eisTraceModChar, IdealGaussCRT.traceModChar_mk, hgen]
  change _ / _ = _ / _
  rw [hsum, hgen]

theorem squarefreeGaussCoefficient_eq_canonicalProductCoefficient {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    squarefreeGaussCoefficient (Ideal.span {∏ i, p i}) =
      FiniteGaussPhase.canonicalProductCoefficient p hp hcop hgood := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  have hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0 := by rwa [hgen]
  have hsq : Squarefree (Ideal.span {∏ i, p i}) := by
    apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (Ideal.span_singleton_eq_bot.not.mpr hpall)).mpr
    rw [normalizedFactors_product]
    apply Multiset.Nodup.map
    · intro i j hij
      by_contra hne
      have ht := (hcop hne).sup_eq
      rw [hij, sup_idem] at ht
      exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
    · exact Finset.univ.nodup
  rw [squarefreeGaussCoefficient_eq _ hsq hI,
    gaussTwo_eq_canonicalProductGauss p hp hcop hgood hprimary hI, hgen]
  rfl

end CompletedGauss

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
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
namespace FirstPassCubeLabels
open ActualEisensteinCubic

section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem row_pow (a : O) (m : ℕ) :
    finiteSquarefreeRow P hg S (a ^ m) = finiteSquarefreeRow P hg S a ^ m := by
  simp only [finiteSquarefreeRow, map_pow, Finset.prod_pow]

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

end Rows

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RayExpansion
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
namespace FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem primeProductNorm_pos {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0) (S : Finset ι) :
    0 < primeProductNorm p S :=
  pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))) 2

end FirstPassCubeLabels

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
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
namespace ActualEisensteinCubic
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCoordinates EisensteinSchwartzPoisson

theorem primeSubsetGenerator_norm_sq {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 = (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ)) (span_idealGenerator _)

end ActualEisensteinCubic

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
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

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_add_frequency (t s x : ℝ) :
    logPhase (t + s) x = logPhase t x * logPhase s x := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] lemma frequencyTwist_twice (g : 𝓢(ℝ, ℂ)) (t s : ℝ) :
    frequencyTwist (frequencyTwist g t) s = frequencyTwist g (t + s) := by
  ext x
  simp only [frequencyTwist_apply, logPhase_add_frequency]
  ring

end JointLogSeparation

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalDifference
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_eq_ideal_norm (S : Finset ι) :
    primeProductNorm p S = (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) := by
  rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    FiniteGaussPhase.span_finset_prod]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_ge_one (S : Finset ι) : 1 ≤ primeProductNorm p S :=
  by
    rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {∏ i ∈ S, p i}) ≠ 0 by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.SupportNorms
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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open FirstPassCubeLabels (columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeSubsetGenerator_norm_eq_productNorm (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 = primeProductNorm p E := by
  rw [primeSubsetGenerator_norm_sq, primeProductNorm_eq_ideal_norm]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.GreenIdentity
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
namespace SecondPassArithmetic

section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

lemma element_norm_ge_one (a : O) (ha : a ≠ 0) : 1 ≤ ‖eisEmbedding a‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {a}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SeedDefects
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

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm squarefreeLabel jLabel j2Label b0Label
  bit parity conductorExponent cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_ne_zero (B : Finset ι) (v : ι → ℕ) : primeProduct p B v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi => pow_ne_zero _ (hp i))

end SecondPassArithmetic

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

open scoped BigOperators Classical SchwartzMap
open MeasureTheory

theorem finite_integral_energy_bound {κ : Type*} [Fintype κ]
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (E : ℝ) (hE : 0≤E)
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀k,Integrable (fun t => b t*φ k t))
    (hbound : ∀t,(∑k,‖φ k t‖^2)≤E) :
    (∑k,‖∫t : ℝ,b t*φ k t‖^2)≤E*(∫t : ℝ,‖b t‖)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ→EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖≤‖b t‖*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE]
    change (∑k,‖b t*φ k t‖^2)≤‖b t‖^2*E
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫t : ℝ,F t)=e.symm (fun k => ∫t : ℝ,b t*φ k t) := by
    rw [show F=(fun t => e.symm (fun k => b t*φ k t)) from rfl,e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫t : ℝ,b t*φ k t)‖≤(∫t : ℝ,‖b t‖)*Real.sqrt E := by
    rw [←he,←integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hs
  simpa [e,mul_comm] using hs

open CanonicalQuadraticSieve ActualEisensteinCubic

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ReopenedFibers
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
namespace SecondPassArithmetic

section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

lemma mem_reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFiber v₁ v₂ ↔
      b.leftExponent=v₁ ∧ b.rightExponent=v₂ ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨h₂,h₁⟩ := Finset.mem_product.mp hA
    exact ⟨rfl,rfl,Finset.mem_powerset.mp h₁,Finset.mem_powerset.mp h₂⟩
  · rintro ⟨hl,hr,hb⟩
    apply Finset.mem_image.mpr
    refine ⟨(b.rightDivisor,b.leftDivisor),?_,?_⟩
    · apply Finset.mem_product.mpr
      have hs : b.support=v₁.support∪v₂.support := by rw [CubeCoordinates.support,hl,hr]
      exact ⟨Finset.mem_powerset.mpr (hs ▸ hb.2),Finset.mem_powerset.mpr (hs ▸ hb.1)⟩
    · exact CubeCoordinates.ext hl.symm hr.symm rfl rfl

lemma mem_reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFamily Q ↔ b.leftExponent ∈ Q ∧ b.rightExponent ∈ Q ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨v,hv,hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    exact ⟨hl ▸ (Finset.mem_product.mp hv).2,hr ▸ (Finset.mem_product.mp hv).1,ha⟩
  · rintro ⟨hl,hr,ha⟩
    exact Finset.mem_biUnion.mpr ⟨(b.rightExponent,b.leftExponent),Finset.mem_product.mpr ⟨hr,hl⟩,
      (mem_reopenedCubeFiber _ _ b).mpr ⟨rfl,rfl,ha⟩⟩

lemma reopenedCubeFamily_admissible (Q : Finset (ι →₀ ℕ)) :
    ∀ b ∈ reopenedCubeFamily Q,b.Admissible :=
  fun b hb => ((mem_reopenedCubeFamily Q b).mp hb).2.2

omit [DecidableEq ι] in
lemma primeProduct_finsupp_support (p : ι → ActualEisensteinCubic.O) (B : Finset ι) (v : ι →₀ ℕ)
    (hv : v.support ⊆ B) : primeProduct p B v=primeProduct p v.support v := by
  unfold primeProduct
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

lemma reopenedCubeFamily_cube_norms (p : ι → ActualEisensteinCubic.O) (Q : Finset (ι →₀ ℕ)) (B : ℝ)
    (hQ : ∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) :
    ∀ b ∈ reopenedCubeFamily Q,
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2 ≤ B ∧
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2 ≤ B := by
  intro b hb
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  rw [primeProduct_finsupp_support p b.support b.leftExponent Finset.subset_union_left,
    primeProduct_finsupp_support p b.support b.rightExponent Finset.subset_union_right]
  exact ⟨hQ _ hl,hQ _ hr⟩

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
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
open scoped BigOperators Classical Topology

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss (actualSextic)

theorem idealRowHom_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (x : ActualEisensteinCubic.O) :
    idealRowHom x (Ideal.span {∏i∈S,p i}) =
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S x := by
  rw [FiniteGaussPhase.span_finset_prod,map_prod]
  simp only [finiteSquarefreeRow]
  apply Finset.prod_congr rfl
  intro i hi
  exact idealRowHom_prime x _ (hg i)

theorem rowTwist_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) :
    rowTwist Ψ m f z (∏i∈S,p i) =
      Ψ (∏i∈S,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) S m*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S f^4*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  change Ψ _ * idealRowHom _ (Ideal.span {∏i∈S,p i}) = _
  rw [idealRowHom_product p hg S,finiteSquarefreeRow_mul,finiteSquarefreeRow_mul,
    FirstPassCubeLabels.row_pow,FirstPassCubeLabels.row_pow,FirstPassCubeLabels.row_sixth]
  ring

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open SecondPassArithmetic hiding O

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem squarefreeGaussCoefficient_finset (hpr : ∀i,lambda^2∣p i-1) (S : Finset ι) :
    squarefreeGaussCoefficient (Ideal.span {∏i∈S,p i}) =
      MixedCrossSeparation.columnCoefficient p hp hcop hg S := by
  have h := squarefreeGaussCoefficient_eq_canonicalProductCoefficient
    (fun i:S=>p i.val) (fun i=>hp i.val)
    (MixedCrossSeparation.columnPrimeCoprime p hcop S) (fun i=>hg i.val)
    (fun i=>hpr i.val)
  simpa only [Finset.prod_coe_sort,MixedCrossSeparation.columnCoefficient] using h

theorem columnWeight_finset (hpr : ∀i,lambda^2∣p i-1)
    (S : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι → ℂ) :
    columnWeight (rowTwist Ψ m f z) (Ideal.span {∏i∈S,p i}) * H S =
      canonicalSourceCoefficient p hp hcop hg Ψ m f H S *
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  have hn : (∏i∈S,p i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hprimary : lambda^2∣(∏i∈S,p i)-1 := by
    have h := product_primary (fun i:S=>p i.val) (fun i=>hpr i.val)
    simpa only [Finset.prod_coe_sort] using h
  rw [columnWeight,squarefreeGaussCoefficient_finset p hp hcop hg hpr S,
    primaryGenerator_span _ hn hprimary,rowTwist_product p hg S]
  simp only [canonicalSourceCoefficient]
  ring

end

end CanonicalRowCompletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Canonical
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_actual_columns
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X =
      ∑ U ∈ pool.powerset,
        columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k)
          (Ideal.span {∏ i ∈ U, p i}) *
        (primeMark slots lists a U * W (primeProductNorm p U / X)) := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  have he := CanonicalRowCompletion.columnWeight_finset p hp hcop hg hpr U Ψ m f k
    (fun U => primeMark slots lists a U * W (primeProductNorm p U / X))
  symm
  convert (preTransparency := .instances) he using 1 ; simp only [secondChildColumn, canonicalSourceCoefficient] ; ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.DescentProfiles
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

lemma schwartz_logPhase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  convert (preTransparency := .instances) schwartz_log_inversion g x using 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  simp only [logPhase, Real.inner_apply]
  congr 1
  push_cast
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.AmbientProfileTower
namespace OAI

namespace SevenEighths.InverseAmbientProfileTower
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open SevenEighths.InverseMoment
noncomputable section

theorem ambientWeight_eq_pow {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) :
    ambientWeight J p = (ambientWeight 1 p)^J := by
  simp [ambientWeight, mul_pow, Finset.prod_pow]

theorem ambientWeight_one_le {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) :
    1 ≤ ambientWeight J p := by
  unfold ambientWeight
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg p.1.1]))
        (one_le_pow₀ (by linarith [norm_nonneg p.1.2.1])))
        (one_le_pow₀ (by linarith [norm_nonneg p.1.2.2])))
    (Finset.one_le_prod (fun i _ => one_le_pow₀ (by linarith [norm_nonneg (p.2 i)])))

private theorem one_add_norm_add_le (x y : ℝ) :
    1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
  have h := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  nlinarith [mul_nonneg hx hy]

private theorem coordinate_factor_le {ι : Type*} [Fintype ι]
    (i : ι) (u : ι → ℝ) :
    1 + ‖u i‖ ≤ ∏ j, (1 + ‖u j‖) :=
  by
  have hm (j : ι) : max (1 + ‖u j‖) 1 = 1 + ‖u j‖ :=
    max_eq_left (by linarith [norm_nonneg (u j)])
  simpa only [hm] using
    Finset.le_prod_max_one (Finset.mem_univ i) (fun j => 1 + ‖u j‖)

theorem inheritedLeft_bound {ι : Type*} [Fintype ι] (i : ι) (p : Ambient ι) :
    1 + ‖inheritedLeft i p‖ ≤ ambientWeight 1 p := by
  have h := (one_add_norm_add_le (p.2 i + p.1.1) (-p.1.2.2)).trans
    (mul_le_mul_of_nonneg_right (one_add_norm_add_le (p.2 i) p.1.1) (by positivity))
  simp only [norm_neg, ← sub_eq_add_neg] at h
  have hc := coordinate_factor_le i p.2
  have ht : (1 + ‖p.1.1‖) * (1 + ‖p.1.2.2‖) ≤
      (1 + ‖p.1.1‖) * (1 + ‖p.1.2.1‖) * (1 + ‖p.1.2.2‖) := by
    nlinarith [norm_nonneg p.1.1, norm_nonneg p.1.2.1, norm_nonneg p.1.2.2,
      mul_nonneg (mul_nonneg (show 0 ≤ 1 + ‖p.1.1‖ by positivity)
        (norm_nonneg p.1.2.1)) (show 0 ≤ 1 + ‖p.1.2.2‖ by positivity)]
  have hh := mul_le_mul hc ht (by positivity)
    (Finset.prod_nonneg (fun j _ => by positivity))
  change _ ≤ (∏ j, (1 + ‖p.2 j‖)) * _ at hh
  exact h.trans (by simpa [ambientWeight, inheritedLeft, mul_comm, mul_left_comm, mul_assoc] using hh)

theorem inheritedRight_bound {ι : Type*} [Fintype ι] (i : ι) (p : Ambient ι) :
    1 + ‖inheritedRight i p‖ ≤ ambientWeight 1 p := by
  have h := inheritedLeft_bound i ((p.1.2.1, p.1.1, p.1.2.2), p.2)
  change 1 + ‖-(p.2 i + p.1.2.1 - p.1.2.2)‖ ≤ _
  rw [norm_neg]
  simpa [inheritedLeft, ambientWeight, mul_comm, mul_left_comm, mul_assoc] using h

theorem first_inherited_left_eq (p : Ambient (Fin 9)) :
    inheritedLeft 7 p = profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 7 := by
  simp [inheritedLeft, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem first_inherited_right_eq (p : Ambient (Fin 9)) :
    inheritedRight 8 p = -profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 8 := by
  simp [inheritedRight, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem second_inherited_left_eq (p : Ambient (Fin 6)) :
    inheritedLeft 4 p = profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 4 := by
  simp [inheritedLeft, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

theorem second_inherited_right_eq (p : Ambient (Fin 6)) :
    inheritedRight 5 p = -profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 5 := by
  simp [inheritedRight, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

end
end SevenEighths.InverseAmbientProfileTower

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFourier
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapFourier
open InverseMoment
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem density_norm (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ‖density g xj t‖=‖(𝓕 g) t‖ := by
  simp only [density,norm_mul,logPhase_norm,mul_one]

lemma fourier_phase_integrable (g : 𝓢(ℝ,ℂ)) (x : ℝ) (a : ℂ) :
    Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x*a) := by
  have h : Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x) (volume:Measure ℝ) :=
    (𝓕 g).integrable.mul_bdd (c:=1)
    (logPhase_continuous_left x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>le_of_eq (logPhase_norm t x)))
  exact h.mul_const a

end SevenEighths.InverseInitialOverlapFourier

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ClippedFourier
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns InverseInitialOverlapFourier SecondPassIntegration JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem clipped_fixed_window (W:ℝ→ℂ) (lo hi b:ℝ) (hlo:0<lo) (hb:1≤b)
    (hW:Function.support W⊆Set.Icc lo hi):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀c,1≤ c→c≤b→∀y,0<y→wFresh y*W (c*y)=W (c*y):=by
  have hb0:0<b:=zero_lt_one.trans_le hb
  let a:=lo/b
  let B:=a+|hi|+1
  have ha:0<a:=div_pos hlo hb0
  obtain ⟨wFresh,hc,hone,hs⟩:=InverseSecondChildWindows.positive_cutoff a B ha (by dsimp [B];linarith [abs_nonneg hi])
  refine ⟨wFresh,a/2,B+1,half_pos ha,by dsimp [B];linarith [abs_nonneg hi],hc,hs,?_⟩
  intro c hc hcb y hy
  by_cases hz:W (c*y)=0
  · simp only [hz,mul_zero]
  have hw:=hW hz
  have hay:a≤y:=by
    apply (div_le_iff₀ hb0).mpr
    calc
      lo≤ c*y:=hw.1
      _≤y*b:=by nlinarith
  have hyhi:y≤hi:=le_trans (by nlinarith) hw.2
  have hyB:y≤B:=by dsimp [B];linarith [le_abs_self hi]
  rw [hone y ⟨hay,hyB⟩,one_mul]

theorem clipped_test_fourier (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ y:ℝ)(hc:0<c)(hy:0<y)(hwFresh:wFresh y*W (c*y)=W (c*y)):
    clippedTest W c θ y =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t *
        childLogTest wFresh (θ+t) y:=by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  change clippedTest W c θ y=∫t:ℝ,density g (Real.log c) t*childLogTest wFresh (θ+t) y
  have he (t:ℝ):density g (Real.log c) t*childLogTest wFresh (θ+t) y=
      ((𝓕 g) t*logPhase t (Real.log c+Real.log y))*(wFresh y*logPhase θ (Real.log y)):=by
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  have hi':(∫t:ℝ,(𝓕 g) t*logPhase t (Real.log c+Real.log y))=W (c*y):=by
    calc
      _=(∫t:ℝ,logPhase t (Real.log c+Real.log y)*(𝓕 g) t):=by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _=g (Real.log c+Real.log y):=(schwartz_logPhase_inversion g _).symm
      _= _:=by
        simp only [g,CubicReflectionKernel.logSchwartz_apply,Real.exp_add,Real.exp_log hc,Real.exp_log hy]
  rw [hi']
  unfold clippedTest childLogTest
  calc
    W (c*y)*logPhase θ (Real.log y)=(wFresh y*W (c*y))*logPhase θ (Real.log y):=by rw [hwFresh]
    _= _:=by ring

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_clipped_mode_integrable
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m f k:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (g:𝓢(ℝ,ℂ))(wFresh:ℝ→ℂ)(c θ X:ℝ):
    Integrable (fun t:ℝ=>density g (Real.log c) t*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (childLogTest wFresh (θ+t)) X):=by
  simp_rw [finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro U hU
  convert (preTransparency := .instances) fourier_phase_integrable g (Real.log c+Real.log (primeProductNorm p U/X))
    (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
      primeMark slots lists a U*wFresh (primeProductNorm p U/X)*logPhase θ (Real.log (primeProductNorm p U/X))) using 1
  funext t
  simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
  ring

theorem canonical_clipped_fourier
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m f k:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:ℝ→ℂ)(lo hi:ℝ)(hlo:0<lo)(hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ X:ℝ)(hc:0<c)(hX:0<X)(hwFresh:∀y,0<y→wFresh y*W (c*y)=W (c*y)):
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (clippedTest W c θ) X=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t *
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (childLogTest wFresh (θ+t)) X:=by
  simp_rw [finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr]
  simp only [Finset.mul_sum]
  have hints (U:Finset ι):Integrable (fun t:ℝ=>
      density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t*
      (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
        (primeMark slots lists a U*childLogTest wFresh (θ+t) (primeProductNorm p U/X)))):=by
    convert (preTransparency := .instances) fourier_phase_integrable (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)
      (Real.log c+Real.log (primeProductNorm p U/X))
      (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
        primeMark slots lists a U*wFresh (primeProductNorm p U/X)*logPhase θ (Real.log (primeProductNorm p U/X))) using 1
    funext t
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  rw [integral_finsetSum _ (fun U _=>hints U)]
  apply Finset.sum_congr rfl
  intro U hU
  rw [clipped_test_fourier W lo hi hlo hs hW wFresh c θ _ hc
    (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U) hX) (hwFresh _ (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U) hX))]
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem finite_weighted_integral_energy {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (w : ℝ → ℝ) (hw : ∀ t,0<w t)
    (E : ℝ) (hE : 0≤E) (hb : Integrable (fun t => w t*‖b t‖))
    (hφ : ∀ k,Integrable (fun t => b t*φ k t))
    (hbound : ∀ t,(∑ k,‖φ k t‖^2)≤E*(w t)^2) :
    (∑ k,‖∫ t : ℝ,b t*φ k t‖^2)≤E*(∫ t : ℝ,w t*‖b t‖)^2 := by
  have hn (t : ℝ) : (w t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw t).ne'
  have hnorm (t : ℝ) : ‖(w t:ℂ)‖=w t := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hw t)]
  have he (k : κ) (t : ℝ) : ((w t:ℂ)*b t)*(φ k t/(w t:ℂ))=b t*φ k t := by
    field_simp [hn t]
  have hh := CompletedGauss.finite_integral_energy_bound
    (fun t => (w t:ℂ)*b t) (fun k t => φ k t/(w t:ℂ)) E hE
    (by simpa only [norm_mul,hnorm] using hb)
    (fun k => by simpa only [he] using hφ k) (fun t => by
      simp only [norm_div,hnorm,div_pow,← Finset.sum_div]
      exact (div_le_iff₀ (sq_pos_of_pos (hw t))).mpr (hbound t))
  simpa only [he,norm_mul,hnorm] using hh

end SevenEighths.CenteredMomentHeckeWindowEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ClippedEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns InverseInitialOverlapFourier CompletedGauss
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem normalized_energy_vector
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(hD:∀f∈labels,0≤D f)
    (W:ℝ→ℂ)(X Z F:ℝ):
    (∑v:labels×rows,‖(Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a W X‖^2)=
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F:=by
  unfold normalizedColumnEnergy
  rw [Fintype.sum_prod_type,←Finset.sum_coe_sort labels]
  apply Finset.sum_congr rfl
  intro f hf
  rw [←Finset.sum_coe_sort rows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_assoc,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hD f f.property)]

theorem canonical_clipped_energy
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(hD:∀f∈labels,0≤D f)
    (W:ℝ→ℂ)(lo hi:ℝ)(hlo:0<lo)(hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ X Z F E:ℝ)(J:ℕ)(hc:0<c)(hX:0<X)(hE:0≤E)
    (hw:∀y,0<y→wFresh y*W (c*y)=W (c*y))
    (he:∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest wFresh s) X Z F≤E*(1+‖s‖)^(2*J)):
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest W c θ) X Z F≤
      E*(1+‖θ‖)^(2*J)*(∫t:ℝ,(1+‖t‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) t‖)^2:=by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  let b:=density g (Real.log c)
  let phi:labels×rows→ℝ→ℂ:=fun v t=>(Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a
      (childLogTest wFresh (θ+t)) X
  have hint(v:labels×rows):Integrable (fun t:ℝ=>b t*phi v t):=by
    convert (preTransparency := .instances) (canonical_clipped_mode_integrable p hp hcop hg hpr pool Ψ m (primaryGenerator v.1) v.2
      slots lists a g wFresh c θ X).const_mul ((Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)) using 1
    funext t
    dsimp [b,phi]
    ring
  have hbound(t:ℝ):(∑v:labels×rows,‖phi v t‖^2)≤
      (E*(1+‖θ‖)^(2*J))*((1+‖t‖)^J)^2:=by
    dsimp only [phi]
    rw [normalized_energy_vector p hp hcop hg pool Ψ m slots lists a labels rows D hD]
    apply (he (θ+t)).trans
    have hb:1+‖θ+t‖≤(1+‖θ‖)*(1+‖t‖):=by
      have hh:=norm_add_le θ t
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg t)]
    calc
      _≤E*((1+‖θ‖)*(1+‖t‖))^(2*J):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) hE
      _= _:=by rw [mul_pow,pow_mul];ring
  have hden:Integrable (fun t:ℝ=>(1+‖t‖)^J*‖b t‖):=by
    simpa only [b,density_norm] using AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hh:=CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy b phi
    (fun t:ℝ=>(1+‖t‖)^J) (by intro t;positivity)
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden hint hbound
  have heq(v:labels×rows): (∫t:ℝ,b t*phi v t)=
      (Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a
        (clippedTest W c θ) X:=by
    rw [canonical_clipped_fourier p hp hcop hg hpr pool Ψ m (primaryGenerator v.1) v.2
      slots lists a W lo hi hlo hs hW wFresh c θ X hc hX hw,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [b,phi,g]
    ring
  simp_rw [heq] at hh
  rw [normalized_energy_vector p hp hcop hg pool Ψ m slots lists a labels rows D hD] at hh
  simpa only [b,density_norm,g] using hh

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ClippedUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem canonical_clipped_uniform
    (W:ℝ→ℂ)(lo hi b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(_hD:∀f∈labels,0≤D f)
      (c θ X Z F E:ℝ),1≤ c→c≤b→0<X→0≤E→
      (∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) X Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (clippedTest W c θ) X Z F≤C*E*(1+‖θ‖)^(2*J):=by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,hagree⟩:=clipped_fixed_window W lo hi b hlo hb hs
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  let M:=(∫t:ℝ,(1+‖t‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) t‖)^2
  refine ⟨M+1,by dsimp [M];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD c θ X Z F E hc1 hcb hX hE he
  have hh:=canonical_clipped_energy p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
    W lo hi hlo hs hW wFresh c θ X Z F E J (zero_lt_one.trans_le hc1) hX hE
    (hagree c hc1 hcb) he
  apply hh.trans
  change E*(1+‖θ‖)^(2*J)*M≤(M+1)*E*(1+‖θ‖)^(2*J)
  have hn:0≤E*(1+‖θ‖)^(2*J):=by positivity
  nlinarith

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondSourceBlocks
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseMoment
open InverseSecondFibers InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem outerNorms_ge_one (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hk : x.second.frequency ≠ 0) :
    ∀ i,1 ≤ outerNorms p x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact element_norm_ge_one _ hk

theorem dyadScale_pos (n : ℕ) : 0 < dyadScale n := by unfold dyadScale; positivity

theorem dyadIndex_bounds (r : ℝ) (hr : 1 ≤ r) :
    dyadScale (dyadIndex r) ≤ r ∧ r < 2*dyadScale (dyadIndex r) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hr
  constructor
  · have h := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hr0).mp (Nat.floor_le hlog)
    simpa only [dyadScale,dyadIndex,Real.rpow_natCast] using h
  · have h := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hr0).mp
      (Nat.lt_floor_add_one (Real.logb 2 r))
    have ht : r < (2:ℝ)^(dyadIndex r+1) := by
      rw [←Real.rpow_natCast]
      simpa only [Nat.cast_add,Nat.cast_one,dyadIndex] using h
    simpa only [dyadScale,pow_succ,mul_comm] using ht

omit [DecidableEq ι] in
theorem cell_subset (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : cell p source d ⊆ source := Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem mem_keys_iff (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : d ∈ keys p source ↔ (cell p source d).Nonempty := by
  simp only [keys,Finset.mem_image,Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨x,hx,he⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨x,(mem_cell p source d x).mpr ⟨hx,he⟩⟩
  · intro h
    obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact ⟨x,(mem_cell p source d x).mp hx⟩

omit [DecidableEq ι] in
theorem cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (i : Fin 4) :
    1 ≤ outerNorms p x i / dyadScale (d i) ∧ outerNorms p x i / dyadScale (d i) < 2 := by
  obtain ⟨hxs,he⟩ := (mem_cell p source d x).mp hx
  have hb := dyadIndex_bounds _ (outerNorms_ge_one p hp x (hk x hxs) i)
  have hi : dyadIndex (outerNorms p x i) = d i := congrFun he i
  rw [hi] at hb
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hb.1),
    (div_lt_iff₀ (dyadScale_pos _)).mpr hb.2⟩

end SevenEighths.InverseSecondSourceBlocks

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

theorem second_cell_column_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    Z^(secondCellColumnExponent Z X d)=X/(scales d 0*scales d 2) := by
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ)
    (div_pos hX (mul_pos (dyadScale_pos _) (dyadScale_pos _)))

theorem second_cell_clipping_ratio (Z X b:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X)
    (hb:1≤b) (hsource:scales d 0*scales d 2≤b*X) :
    1≤Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d) ∧
    Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d)≤b := by
  let N:=secondCellColumnExponent Z X d
  have hz:0<Z:=lt_trans zero_lt_one hZ
  have hn:Z^N=X/(scales d 0*scales d 2):=second_cell_column_scale Z X d hZ hX
  constructor
  · exact Real.one_le_rpow hZ.le (sub_nonneg.mpr (le_max_right _ _))
  · by_cases hN:0≤N
    · rw [max_eq_right hN,sub_self,Real.rpow_zero];exact hb
    · have hN':N≤0:=le_of_not_ge hN
      rw [max_eq_left hN',zero_sub,Real.rpow_neg hz.le,hn,inv_div]
      exact (div_le_iff₀ hX).mpr hsource

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ClippedChild
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns JointLogSeparation InverseAmbientProfileTower
open InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

theorem second_child_height_budget (J:ℕ)(right:Bool)(t:Ambient (Fin 6)):
    (1+‖secondChildHeight right t‖)^J≤tripleHeight J t.1*coordinateHeight J t.2:=by
  cases right
  · have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedLeft 4 t‖) (inheritedLeft_bound 4 t) J
    rw [←ambientWeight_eq_pow] at h
    simpa only [secondChildHeight,Bool.false_eq_true,ite_false,norm_neg,
      second_inherited_left_eq,ambientWeight,tripleHeight,coordinateHeight] using h
  · have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedRight 5 t‖) (inheritedRight_bound 5 t) J
    rw [←ambientWeight_eq_pow] at h
    simpa only [secondChildHeight,ite_true,second_inherited_right_eq,norm_neg,
      ambientWeight,tripleHeight,coordinateHeight] using h

theorem canonical_actual_child_uniform
    (W:ℝ→ℂ)(lo hi b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(_hD:∀f∈labels,0≤D f)
      (Z X F E:ℝ)(d:BlockIndex)(right:Bool)(t:Ambient (Fin 6)),
      1<Z→0<X→scales d 0*scales d 2≤b*X→0≤E→
      (∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) (Z^(max 0 (secondCellColumnExponent Z X d))) Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (clippedTest W (Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d))
          (secondChildHeight right t)) (Z^(max 0 (secondCellColumnExponent Z X d))) Z F≤
        C*E*(tripleHeight (2*J) t.1*coordinateHeight (2*J) t.2):=by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,he⟩:=canonical_clipped_uniform W lo hi b hlo hb hs hW
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  obtain ⟨C,hC,hbound⟩:=he J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD Z X F E d right t hZ hX hgeom hE hmoment
  obtain ⟨hc1,hcb⟩:=second_cell_clipping_ratio Z X b d hZ hX hb hgeom
  have hz:0<Z:=zero_lt_one.trans hZ
  exact (hbound p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
    _ (secondChildHeight right t) _ Z F E hc1 hcb (Real.rpow_pos_of_pos hz _) hE hmoment).trans
      (mul_le_mul_of_nonneg_left (second_child_height_budget (2*J) right t) (mul_nonneg hC.le hE))

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceIndex
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

lemma mem_firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : FirstOriginalOuter ι) :
    k∈firstOriginalOuter pool Q ↔ k.1∈reopenedCubeFamily Q ∧ k.2.1∈(pool\k.1.support).powerset ∧
      k.2.2∈(k.2.1∪cubePrincipalSupport k.1.support k.1.leftExponent k.1.rightExponent k.1.leftBit k.1.rightBit).powerset := by
  simp [firstOriginalOuter]

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstHeightBudget
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open JointLogSeparation InverseAmbientProfileTower

theorem first_left_height_budget (J:ℕ)(p:Ambient (Fin 9)):
    (1+‖profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 7‖)^J≤
      tripleHeight J p.1*coordinateHeight J p.2:=by
  have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedLeft 7 p‖) (inheritedLeft_bound 7 p) J
  rw [←ambientWeight_eq_pow] at h
  simpa only [first_inherited_left_eq,ambientWeight,tripleHeight,coordinateHeight] using h

theorem first_right_height_budget (J:ℕ)(p:Ambient (Fin 9)):
    (1+‖profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 8‖)^J≤
      tripleHeight J p.1*coordinateHeight J p.2:=by
  have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedRight 8 p‖) (inheritedRight_bound 8 p) J
  rw [←ambientWeight_eq_pow] at h
  simpa only [first_inherited_right_eq,norm_neg,ambientWeight,tripleHeight,coordinateHeight] using h

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.PrioritySourceBudget
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

theorem source_cell_joint_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (hk:∀x∈source,x.second.frequency≠0)
    (b X:ℝ) (hgeom:∀x∈source,primeProductNorm p x.second.sourceCommon*
      primeProductNorm p x.second.overlap≤b*X) (d:BlockIndex) (hd:d∈keys p source):
    scales d 0*scales d 2≤b*X := by
  obtain ⟨x,hx⟩:=(mem_keys_iff p source d).mp hd
  have h0:scales d 0≤primeProductNorm p x.second.sourceCommon:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).1
  have h2:scales d 2≤primeProductNorm p x.second.overlap:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 2).1
  exact (mul_le_mul h0 h2 (dyadScale_pos _).le (primeProductNorm_pos p hp _).le).trans
    (hgeom x (cell_subset p source d hx))

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.FirstGlobalParents
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open FirstCauchyArithmetic RayFourExpansion InverseMoment
open InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InversePrioritySecondSource
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

theorem mem_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (x : Source ι 0) :
    x∈originalParentSource pool Q selector ↔
      ∃k∈firstOriginalOuter pool Q,∃D∈pool.powerset,
        selector k D≠0 ∧ fillFirstQuotient (ofOriginal k) D=x := by
  simp only [originalParentSource,globalParentSource,Finset.mem_biUnion,
    originalOuterSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨k,hk,D,hD,by simpa using hs,he⟩
  · rintro ⟨k,hk,D,hD,hs,he⟩
    exact ⟨ofOriginal k,⟨k,hk,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_fill_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : FirstOriginalOuter ι) (hk : k∈firstOriginalOuter pool Q) (D : Finset ι) :
    SourceValid p (fillFirstQuotient (ofOriginal k) D) := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  refine ⟨reopenedCubeFamily_admissible Q k.1 hb,?_,?_,?_⟩
  · exact Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hC hi)).2 hiB)
  · exact (Finset.mem_powerset.mp hE).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))
  · exact fun i=>Fin.elim0 i

variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseFirstGlobalParents

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.FirstGlobalCaps
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalCaps
open InverseMoment InverseFirstGlobalParents InverseFirstPriorityParents
open InverseMomentWholePriorityParents InverseMomentFirstChildWindows
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open ConcreteTraceCRT (eisEmbedding)
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem mem_parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (x : Source ι 0) : x∈parentCell p pool Q selector k l ↔
    ∃o∈outerCell p pool Q k,∃D∈pool.powerset,
      commonSelector p (selector o) l D≠0 ∧ fillFirstQuotient (ofOriginal o) D=x := by
  simp only [parentCell,outerCell,Finset.mem_filter,mem_originalParentSource]
  constructor
  · rintro ⟨⟨o,ho,D,hD,hs,rfl⟩,hg⟩
    exact ⟨o,⟨ho,by simpa using hg⟩,D,hD,hs,rfl⟩
  · rintro ⟨o,⟨ho,hg⟩,D,hD,hs,rfl⟩
    exact ⟨⟨o,ho,D,hD,hs,rfl⟩,by simpa using hg⟩

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerNorms_ge_one (x : FirstOriginalOuter ι) : ∀i,1≤outerNorms p x i := by
  intro i
  fin_cases i
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  · exact primeProductNorm_ge_one p hp _
  · change 1≤‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerGate_dyads (k : SourceIndex) (x : FirstOriginalOuter ι) (hx : outerGate p k x) :
    ∀i : Fin 5,dyadScale (k i.castSucc)≤outerNorms p x i ∧
      outerNorms p x i≤2*dyadScale (k i.castSucc) := by
  intro i
  have h:=dyadIndex_bounds _ (outerNorms_ge_one p hp x i)
  rw [hx i] at h
  exact ⟨h.1,h.2.le⟩

omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma commonSelector_norm (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) :
    ‖commonSelector p selector l D‖≤‖selector D‖ := by
  unfold commonSelector
  split_ifs <;> simp

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma live_common_dyads (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι)
    (hlive : commonSelector p selector l D≠0) :
    dyadScale l≤primeProductNorm p D ∧ primeProductNorm p D≤2*dyadScale l := by
  have he : dyadIndex (primeProductNorm p D)=l := by
    by_contra h
    exact hlive (by simp [commonSelector,h])
  have h:=dyadIndex_bounds _ (primeProductNorm_ge_one p hp D)
  rw [he] at h
  exact ⟨h.1,h.2.le⟩

omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
lemma sourceIdeal_norm (D : Finset ι) : (Ideal.absNorm (sourceIdeal p D):ℝ)=primeProductNorm p D := by
  simp only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm]

omit [∀i,(Ideal.span {p i}).IsMaximal] in

theorem parentCell_cube_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z ell eta : ℝ)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
    ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  exact reopenedCubeFamily_cube_norms p Q _ hQ o.1
    ((mem_firstOriginalOuter pool Q o).mp (Finset.mem_filter.mp ho).1).1

lemma rpow_dyadicExponent (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    Z^dyadicExponent Z n=dyadScale n :=
  Real.rpow_logb (by linarith) (by linarith) (dyadScale_pos n)

lemma dyad_power_bounds (Z eta q : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta) (n : ℕ)
    (hq : dyadScale n≤q ∧ q≤2*dyadScale n) :
    Z^dyadicExponent Z n≤q ∧ q≤Z^(dyadicExponent Z n+eta) := by
  rw [Real.rpow_add (by linarith),rpow_dyadicExponent Z hZ]
  refine ⟨hq.1,hq.2.trans ?_⟩
  nlinarith [dyadScale_pos n]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_norm_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (∀i : Fin 5,Z^dyadicExponent Z (k i.castSucc)≤outerNorms p (toOriginal x) i ∧
      outerNorms p (toOriginal x) i≤Z^(dyadicExponent Z (k i.castSucc)+eta)) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)=primeProductNorm p x.quotientSupport ∧
    Z^dyadicExponent Z l≤(Ideal.absNorm (parent p x).quotient:ℝ) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)≤Z^(dyadicExponent Z l+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  have hg := outerGate_dyads p hp k o (Finset.mem_filter.mp ho).2
  have hd := live_common_dyads p hp (selector o) l D hs
  simp only [toOriginal_fill,toOriginal_ofOriginal]
  refine ⟨fun i=>dyad_power_bounds Z eta _ hZ h2 _ (hg i),sourceIdeal_norm p D,?_⟩
  change Z^dyadicExponent Z l≤(Ideal.absNorm (sourceIdeal p D):ℝ) ∧
    (Ideal.absNorm (sourceIdeal p D):ℝ)≤Z^(dyadicExponent Z l+eta)
  rw [sourceIdeal_norm]
  exact dyad_power_bounds Z eta _ hZ h2 l hd

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_ideal_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (Z^dyadicExponent Z (k 2)≤primeProductNorm p x.firstCommon ∧
      primeProductNorm p x.firstCommon≤Z^(dyadicExponent Z (k 2)+eta)) ∧
    (Z^dyadicExponent Z (k 3)≤(Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ)≤Z^(dyadicExponent Z (k 3)+eta)) ∧
    (Z^dyadicExponent Z (k 4)≤(Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ)
        ≤Z^(dyadicExponent Z (k 4)+eta)) := by
  have h:=(parentCell_norm_bounds p hp pool Q selector k l Z eta hZ h2 x hx).1
  refine ⟨h 2,?_,?_⟩
  · simpa [sourceIdeal_norm,outerNorms,toOriginal,primeSubsetGenerator_norm_eq_productNorm] using h 3
  · simpa [sourceIdeal_norm,outerNorms,toOriginal] using h 4

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem labelParentCell_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈labelParentCell p pool Q selector k l j) :
    x∈parentCell p pool Q selector k l ∧
    Z^dyadicExponent Z j≤jNorm p (toOriginal x) ∧
      jNorm p (toOriginal x)≤Z^(dyadicExponent Z j+eta) := by
  obtain ⟨hm,hj⟩:=Finset.mem_filter.mp hx
  have hn : 1≤jNorm p (toOriginal x) :=
    EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  have hd:=dyadIndex_bounds _ hn
  rw [hj] at hd
  exact ⟨hm,dyad_power_bounds Z eta _ hZ h2 j ⟨hd.1,hd.2.le⟩⟩

end SevenEighths.InverseFirstGlobalCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondUniformCutoff
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseSecondSourceBlocks InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma uniformSecondRadius_nonneg {ι : Type*} [DecidableEq ι] (p : ι→O)
    (Z delta eta : ℝ) (G E : Finset ι) (L Y H : ℝ)
    (hZ : 0≤Z) (hY : 0≤Y) (hH : 0≤H) :
    0≤uniformSecondRadius p Z delta eta G E L Y H := by
  unfold uniformSecondRadius
  positivity

theorem correlated_le_uniform {ι : Type*} [DecidableEq ι] (p : ι→O)
    (Z delta eta : ℝ) (d : O) (G E : Finset ι) (L Y H : ℝ)
    (hY : 0<Y) (hH : 0≤H) (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta)) :
    correlatedSecondRadius p d G E L Y H≤uniformSecondRadius p Z delta eta G E L Y H := by
  unfold correlatedSecondRadius uniformSecondRadius
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (sq_nonneg _)) (sq_nonneg _)) hH) hY.le

end SevenEighths.InverseSecondUniformCutoff
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepGates
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

lemma extra_subset (negative : Bool) (c : CubeCoordinates ι) : extra negative c⊆c.support := by
  cases negative
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

lemma dyadic_exponent_nonneg (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    0≤InverseFirstGlobalCaps.dyadicExponent Z n :=
  Real.logb_nonneg hZ (by unfold dyadScale;exact one_le_pow₀ (by norm_num : (1:ℝ)≤2))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma label_parent_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,SourceValid p y := by
  intro y hy
  obtain ⟨o,ho,D,hD,hs,rfl⟩ := (InverseFirstGlobalCaps.mem_parentCell p pool Q (fun _ _=>1) k l y).mp
    (Finset.mem_filter.mp hy).1
  exact original_fill_valid p pool Q o (Finset.mem_filter.mp ho).1 D

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem label_parent_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) (Z ell eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport y.cube.support
        (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)
        ≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 4)+eta) ∧
      primeProductNorm p y.firstCommon≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 2)+eta) ∧
      primeProductNorm p y.quotientSupport≤Z^(InverseFirstGlobalCaps.dyadicExponent Z l+eta) ∧
      Z^(InverseFirstGlobalCaps.dyadicExponent Z j-eta)≤InverseFirstGlobalCaps.jNorm p (toOriginal y) ∧
      InverseFirstGlobalCaps.jNorm p (toOriginal y)≤Z^(InverseFirstGlobalCaps.dyadicExponent Z j+eta) ∧
      primeProductNorm p y.firstDivisor≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 3)+eta) := by
  intro y hy
  have hparent := (Finset.mem_filter.mp hy).1
  have hc := InverseFirstGlobalCaps.parentCell_cube_bounds p pool Q (fun _ _=>1) k l Z ell eta hQ y hparent
  have hn := InverseFirstGlobalCaps.parentCell_norm_bounds p hp pool Q (fun _ _=>1) k l Z eta hZ hbin y hparent
  have hi := InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l Z eta hZ hbin y hparent
  have hj := InverseFirstGlobalCaps.labelParentCell_bounds p hp pool Q (fun _ _=>1) k l j Z eta hZ hbin y hy
  refine ⟨hc.1,hc.2,?_,hi.1.2,?_,?_,hj.2.2,?_⟩
  · simpa only [InverseFirstGlobalCaps.sourceIdeal_norm] using hi.2.2.2
  · simpa only [hn.2.1] using hn.2.2.2
  · exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hj.2.1
  · simpa only [InverseFirstGlobalCaps.sourceIdeal_norm] using hi.2.1.2

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepPhysicalGates
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0)

lemma parentWeight_norm (l : ℕ) (x : Source ι 0) : ‖parentWeight p l x‖≤1 := by
  simp only [parentWeight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  simpa using InverseFirstGlobalCaps.commonSelector_norm p (fun _=>1) l x.quotientSupport

lemma secondCutoff_nonneg (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (hZ : 0<Z) (G E : Finset ι) :
    0≤ secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  apply uniformSecondRadius_nonneg _ _ _ _ _ _ _ _ _ hZ.le
  · unfold firstCellRadius
    positivity
  · exact Real.rpow_nonneg hZ.le _

include hp in
theorem secondCutoff_dominates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (Z M r ell V eta tau window : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,∀G E : Finset ι,
      correlatedSecondRadius p (secondParentDivisor p (parent p y)) G E
        (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)≤
      secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  intro y hy G E
  have hd := (InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l
    Z eta hZ hbin y (Finset.mem_filter.mp hy).1).2.1.2
  apply correlated_le_uniform p Z (exponent Z (k 3)) eta _ G E _ _ _
    (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  simpa [secondParentDivisor,parent,InverseFirstGlobalCaps.sourceIdeal_norm,
    primeSubsetGenerator_norm_eq_productNorm] using hd

include hp in
theorem parent_tail_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (Z ell eta Lcap : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hcap : 0≤Lcap)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hell : ell+eta≤Lcap) (hactive : exponent Z (k 4)+eta≤Lcap)
    (hcommon : exponent Z (k 2)+eta≤Lcap) (hquot : exponent Z l+eta≤Lcap) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^Lcap ∧
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^Lcap ∧
      ‖eisEmbedding (∏i∈cubeActiveSupport y.cube.support
        (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i)‖≤Z^Lcap ∧
      primeProductNorm p y.firstCommon≤Z^Lcap ∧ primeProductNorm p y.quotientSupport≤Z^Lcap := by
  intro y hy
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ y hy
  have hpw {a : ℝ} (ha : a≤Lcap) : Z^a≤Z^Lcap := Real.rpow_le_rpow_of_exponent_le hZ.le ha
  refine ⟨hb.1.trans (hpw hell),hb.2.1.trans (hpw hell),?_,
    hb.2.2.2.1.trans (hpw hcommon),hb.2.2.2.2.1.trans (hpw hquot)⟩
  have he := hb.2.2.1.trans (hpw hactive)
  have hone := Real.one_le_rpow hZ.le hcap
  change ‖eisEmbedding (∏i∈_,p i)‖^2≤Z^Lcap at he
  have hn := norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i))
  nlinarith

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFixedChildStepUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_fixed_child_step_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (bcap:ℝ)(hbcap:1≤bcap)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → b≤bcap → (slots:Set σ).PairwiseDisjoint lists→slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ s:ℝ,∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (childLogTest ω₁ s)
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(1+‖s‖)^(2*J)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ s:ℝ,∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (childLogTest ω₂ s)
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(1+‖s‖)^(2*J))) →
      Jo≤Jmax→0≤ell+eta→0≤Bfirst→0≤j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤pi+eta/2→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(tcount+eta))→
      1≤Y→1≤X*Real.exp window→Y≤Z^Lcap→Y⁻¹≤Z^Lcap→X*Real.exp window≤Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤Lcap→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^Lcap)→
      (∀G E,0≤ cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤ cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*J))*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨v₁,v₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hstep⟩:=
    global_priority_filtered_physical_step_uniform_types  om lo hi hlo hsupport negative
      window Lcap tau saving hhi hLcap htau Jmax dsmall hdsmall caps hcaps B₀ hB₀ K εmass hεmass
  obtain ⟨w₁,a₁,b₁,ha₁,hab₁,hw₁,hsw₁,hfixed₁⟩:=canonical_actual_child_uniform
    v₁ af bf bcap haf hbcap ((subset_tsupport _).trans hs₁) (v₁.smooth ⊤)
  obtain ⟨w₂,a₂,b₂,ha₂,hab₂,hw₂,hsw₂,hfixed₂⟩:=canonical_actual_child_uniform
    v₂ af bf bcap haf hbcap ((subset_tsupport _).trans hs₂) (v₂.smooth ⊤)
  refine ⟨w₁,w₂,min a₁ a₂,max b₁ b₂,lt_min ha₁ ha₂,
    (min_le_left _ _).trans (hab₁.trans (le_max_left _ _)),hw₁,hw₂,
    hsw₁.trans (Set.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _)),
    hsw₂.trans (Set.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)),?_⟩
  intro J
  obtain ⟨C₁,hC₁,he₁⟩:=hfixed₁ J
  obtain ⟨C₂,hC₂,he₂⟩:=hfixed₂ J
  obtain ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,he⟩:=hstep (2*J)
  let Cmax:=max C₁ C₂
  have hmax:0≤Cmax:=hC₁.le.trans (le_max_left _ _)
  refine ⟨C*Cmax,Cbin,Czero,Ctail,mul_nonneg hC hmax,hCbin,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hbcap' hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hout:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels (Cmax*A)
    hhib hdisj hslots (mul_nonneg hmax hA)
  have hnew:
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*(Cmax*A)*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*J))*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
    apply hout
    · intro ray core assigned hassigned
      obtain ⟨haa,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hb₁,hb₂,hactive',hj',hq,hΨ,
        hal,har,hlabels,ho,hsl,hsr,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned hassigned
      refine ⟨haa,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hb₁,hb₂,hactive',hj',hq,hΨ,
        hal,har,hlabels,ho,hsl,hsr,mul_nonneg hmax hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,?_,?_⟩
      · intro z d hd u J₁ hJ₁ γ hγ
        have hgeomcell:=source_cell_joint_bound p hp _ (fun x hx=>(Finset.mem_erase.mp (hrows x hx)).1) b X hgeom d hd
        have hh:=he₁ p hp hcop hg hpr pool _ _ ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (fun f hf=>pow_nonneg (Nat.cast_nonneg _) _) Z X _
          (A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild)) d false u hZ hX
          (hgeomcell.trans (mul_le_mul_of_nonneg_right hbcap' hX.le)) (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
          (fun s=>hleft z d hd s J₁ hJ₁ γ hγ)
        change _≤(Cmax*A)*Z^(_)*_
        apply hh.trans
        have hH:0≤tripleHeight (2*J) u.1*coordinateHeight (2*J) u.2:=by
          unfold tripleHeight coordinateHeight
          positivity
        have hE:0≤A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild):=
          mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        convert (preTransparency := .instances) mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hE) hH using 1 ; ring
      · intro z d hd u J₂ hJ₂ γ hγ
        have hgeomcell:=source_cell_joint_bound p hp _ (fun x hx=>(Finset.mem_erase.mp (hrows x hx)).1) b X hgeom d hd
        have hh:=he₂ p hp hcop hg hpr pool _ _ ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (fun f hf=>pow_nonneg (Nat.cast_nonneg _) _) Z X _
          (A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild)) d true u hZ hX
          (hgeomcell.trans (mul_le_mul_of_nonneg_right hbcap' hX.le)) (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
          (fun s=>hright z d hd s J₂ hJ₂ γ hγ)
        change _≤(Cmax*A)*Z^(_)*_
        apply hh.trans
        have hH:0≤tripleHeight (2*J) u.1*coordinateHeight (2*J) u.2:=by
          unfold tripleHeight coordinateHeight
          positivity
        have hE:0≤A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild):=
          mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        convert (preTransparency := .instances) mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hE) hH using 1 ; ring
    all_goals assumption
  convert (preTransparency := .instances) hnew using 1 ; ring
end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStep
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondFibers InverseInitialClippedColumns RayFourExpansion FirstCauchyArithmetic
open InverseWholePriorityRetainedSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem actual_label_cell_step (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
    (hsupport : Function.support om⊆Set.Icc lo hi) (negative : Bool)
    (window Ltail Lgate tau saving : ℝ) (hhi : hi≤Real.exp window)
    (hLtail : 0≤Ltail) (hLgate : 0≤Lgate) (htau : 0<tau)
    (bcap : ℝ) (hbcap : 1≤bcap) (dsmall : ℝ) (hdsmall : 0<dsmall)
    (B₀ : Fin 6→ℝ) (hB₀ : ∀i,0≤B₀ i) (K : ℕ) (epsmass : ℝ) (hepsmass : 0<epsmass) :
    ∃(ω₁ ω₂ : 𝓢(ℝ,ℂ))(loFresh hiFresh : ℝ),0<loFresh ∧ loFresh≤hiFresh ∧
      HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
    ∀degree : ℕ,∃C Cbin Czero Ctail : ℝ,0≤C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ : Type}[DecidableEq ι][DecidableEq σ](p : ι→O)(hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι)(Q : Finset (ι→₀ℕ))(k : SourceIndex)(l j : ℕ)
      (Ψ : O→*ℂ)(m : O)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ)
      (Z M r ell V eta pi b Lcol LY epschild A t : ℝ)(ρ : Fin 6→ℝ),
      2≤Z→0≤eta→2≤Z^eta→0≤ell+eta→
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (slots:Set σ).PairwiseDisjoint lists→slots.card≤K→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      (∀u,‖Ψ u‖≤1)→(∀i,|ρ i|≤B₀ i)→hi≤b→b≤bcap→1≤b→b≤Z^(6*eta)→
      Real.exp window≤Z^(4*eta)→0≤A→
      columnScale Z r k l negative*Real.exp window≤Z^Lcol→
      (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY→
      b*columnScale Z r k l negative≤Z^Lgate→exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lgate→
      epsmass*(ell+exponent Z (k 4)/2+exponent Z l+Lgate+11*eta/2)≤pi→
      epsmass*(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)+7*eta/2+
        dsmall*(3*ell+exponent Z (k 2)+exponent Z l+5*eta)+
        2*epsmass*(2*ell+exponent Z (k 2)+exponent Z l+4*eta)≤pi+eta/2→
      1≤firstCellRadius Z M r ell V eta tau k j→1≤ columnScale Z r k l negative*Real.exp window→
      firstCellRadius Z M r ell V eta tau k j≤Z^Ltail→
      (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^Ltail→
      columnScale Z r k l negative*Real.exp window≤Z^Ltail→
      firstKappa M r ell V (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) (exponent Z (k 4))+
        (9/2:ℝ)*eta≤Ltail→
      ell+eta≤Ltail→exponent Z (k 4)+eta≤Ltail→exponent Z (k 2)+eta≤Ltail→exponent Z l+eta≤Ltail→
      ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree→
      (Z^(firstKappa M r ell V (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) (exponent Z (k 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j) (parentWeight p l)
        negative Ψ m slots lists a om (columnScale Z r k l negative) t (firstCellRadius Z M r ell V eta tau k j)≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*degree))*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+epschild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,hstep⟩ := global_priority_fixed_child_step_uniform_types
    om lo hi hlo hsupport negative window Ltail tau saving hhi hLtail htau bcap hbcap
    0 dsmall hdsmall (fun _=>Lgate) (fun _=>hLgate) B₀ hB₀ K epsmass hepsmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree
  obtain ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,he⟩ := hstep degree
  refine ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q k l j Ψ m slots lists a
    Z M r ell V eta pi b Lcol LY epschild A t ρ hZ2 heta hbin hell hQ hdisj hslots ha hΨ hρ hhib hbb hb1 hb6
    hwindow hA hcol hYi hgeom hphysical hbudget hcost hY1 hX1 hYcap hYicap hXcap hPcap hellcap hactivecap hcommoncap hquotcap hchild
  have hZ : 1<Z := by linarith
  have hz : 0<Z := zero_lt_one.trans hZ
  have hX : 0<columnScale Z r k l negative := Real.rpow_pos_of_pos hz _
  have hY : 0<firstCellRadius Z M r ell V eta tau k j := Real.rpow_pos_of_pos hz _
  have hparent := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  have htail := parent_tail_caps p hp pool Q k l j Z ell eta Ltail hZ heta hbin hLtail hQ
    hellcap hactivecap hcommoncap hquotcap
  apply he p hp hcop hg hpr hinj hc (extra negative) pool
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    (label_parent_valid p pool Q k l j) (fun y hy=>extra_subset negative y.cube)
    (parentWeight p l) (fun y hy=>parentWeight_norm p l y) Ψ m slots lists a
    (secondCutoff p Z M r ell V eta tau window k l j negative)
    (firstCellRadius Z M r ell V eta tau k j)
    (fun _ d=>actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
    (eta*Real.log Z) Z (columnScale Z r k l negative) epschild
    (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta)
    ell (exponent Z (k 4)) (exponent Z j) (exponent Z l) eta M r V
    (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) pi b ρ t
    (fun assigned d=>actualCellLabels p (source p pool Q k l j negative assigned lists Z M r ell V eta tau window b) d) A
    hhib hbb hdisj hslots hA
  · intro ray core assigned hassigned
    obtain ⟨_,_,hrows,_,hn,hlabels,_,hcaps,hgeometry,hmass⟩ := source_step_arithmetic p hp pool Q k l j
      negative assigned lists Z M r ell V eta tau window b Lcol LY Lgate epsmass pi
      hZ heta hbin hepsmass.le hwindow hQ hcol hYi hgeom hphysical hbudget
    have hJ : assigned.card≤K := (Finset.card_le_card hassigned).trans hslots
    have hrest : (slots\assigned).card≤K := (Finset.card_le_card Finset.sdiff_subset).trans hslots
    have hbchild := hchild ray core assigned hassigned
    refine ⟨(fun i hi q hq=>ha i (hassigned hi) q hq),hρ,mul_nonneg heta (Real.log_nonneg hZ.le),hZ,hX,hY,heta,hbin,
      hrows,(fun x hx=>(hn x hx).1),(fun x hx=>(hn x hx).2.1),(fun x hx=>(hn x hx).2.2.1),
      (fun x hx=>(hn x hx).2.2.2.2.2.1),(fun x hx=>(hn x hx).2.2.2.2.1),hΨ,
      (fun i hi q hq=>ha i (Finset.mem_sdiff.mp hi).1 q hq),
      (fun i hi q hq=>ha i (Finset.mem_sdiff.mp hi).1 q hq),
      (fun d hd x hx=>hlabels d x hx),by omega,hrest,hrest,hA,rfl,rfl,rfl,(fun _=>rfl),hZ2,hb1,hb6,
      hcaps,hgeometry,hmass,hbchild.1,hbchild.2⟩
  · exact Nat.zero_le _
  · exact hell
  · exact dyadic_exponent_nonneg Z hZ _
  · exact dyadic_exponent_nonneg Z hZ _
  · exact hcost
  · exact fun y hy=>(hparent y hy).1
  · exact fun y hy=>(hparent y hy).2.1
  · exact fun y hy=>(hparent y hy).2.2.1
  · exact fun y hy=>(hparent y hy).2.2.2.1
  · exact fun y hy=>(hparent y hy).2.2.2.2.1
  · exact hY1
  · exact hX1
  · exact hYcap
  · exact hYicap
  · exact hXcap
  · exact hPcap
  · exact fun y hy=>(htail y hy).1
  · exact fun y hy=>(htail y hy).2.1
  · exact fun y hy=>(htail y hy).2.2.1
  · exact fun y hy=>(htail y hy).2.2.2.1
  · exact fun y hy=>(htail y hy).2.2.2.2
  · exact fun G E=>secondCutoff_nonneg p Z M r ell V eta tau window k l j negative hz G E
  · exact fun y hy G hG E=>secondCutoff_dominates p hp pool Q k l j negative Z M r ell V eta tau window hZ hbin y hy G E.val

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLiveActualStep
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_label_step
    (old:ℝ → ℂ)(oldb:ℝ)(hsold:∀y,old y≠0 → y≤oldb)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)(negative:Bool)
    (F tau saving window b em ed:ℝ)(hF:0≤F)(htau:0<tau)(hb:1≤b)
    (hhib:hi≤b)(hwindow: b≤Real.exp window)(hold:oldb≤Real.exp window)(hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁ ω₂:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (ω₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂:ℝ → ℂ) ∧
      tsupport (ω₁:ℝ → ℂ)⊆Set.Icc af bf ∧ tsupport (ω₂:ℝ → ℂ)⊆Set.Icc af bf ∧
    ∀degree:ℕ,∃C Cbin Cz Ct:ℝ,0≤C ∧ 0≤Cbin ∧ 0≤Cz ∧ 0≤Ct ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι → O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι →₀ ℕ))(labels:Finset (Ideal O))(β:Ideal O → (ι →₀ ℕ) → ℂ)
      (Ψ:O →* ℂ)(m:O)(slots:Finset σ)(lists:σ → Finset ι)(weights:σ → ι → ℂ)
      (Φ:𝓢(ℝ,ℂ))(Z M r ell V eta pi epschild A theta t Kphysical:ℝ),
      2≤Z → 2≤Z^eta → 0≤M → M≤F →  (-eta≤ r)  → r≤F → 0≤ell → ell≤F → 0≤V → V≤F →
      0≤eta → eta≤1 → tau≤1 → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
      em*(20*(3*F+16)+30)≤pi/4 → ed*(20*(3*F+16)+30)≤pi/4 →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀u,‖Ψ u‖≤1) → (slots:Set σ).PairwiseDisjoint lists → slots.card≤K →
      (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) → 0≤A →
      let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource old theta (y/Z^r);
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
      ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ Kphysical),
      ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 negative Ψ m slots lists weights ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree →
      (Z^(firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2) (parentWeight p k.2.1)
        negative Ψ m slots lists weights om (columnScale Z r k.1 k.2.1 negative) t (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤
      Cz*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*degree))*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+epschild)+Ct*Z^(-saving):=by
  let cap:=3*F+16
  have hcap:0≤ cap:=by dsimp [cap];linarith
  have hbig:0≤16*cap+20:=by positivity
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,he⟩:=actual_label_cell_step om lo hi hlo hs negative
    window (16*cap+20) (16*cap+20) tau saving (hhib.trans hwindow) hbig hbig htau b hb ed hed (fun _=>0) (by intro i;norm_num) K em hem
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree
  obtain ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,hstep⟩:=he degree
  refine ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta t Kphysical hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1
    hwin hpi hetapi hsmall hsmall' hQ hn hΨ hslots hcard hw hA cutoff W mark S k hk hchild
  have hZ1:1<Z:=by linarith
  have hz:0<Z:=by linarith
  obtain ⟨hY1,hX1,hcol,hYcap,hYi,hgeom,hphysical,hPcap,hbudget,hcost,hellcap,hactivecap,hcommoncap,hquotcap⟩:=
    original_live_step_scalars p hp hcop hg pool Q labels β Ψ m mark old Φ Kphysical Z M r ell V F eta tau theta oldb b window em ed pi
      hZ1 hbin hF hM hMF hr hrF hell hellF hV hVF heta heta1 htau.le htau1 hwin hold hwindow hem.le hed.le hpi hetapi
      hsmall hsmall' hQ hn hsold k hk negative
  apply hstep p hp hcop hg hpr hinj hc pool Q k.1 k.2.1 k.2.2 Ψ m slots lists weights
    Z M r ell V eta pi b (cap+1) (4*cap+2) epschild A t (fun _=>0)
    hZ heta hbin (by linarith) hQ hslots hcard hw hΨ (by intro i;simp) hhib le_rfl hb
  · exact (hwindow.trans hwin).trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hwin.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hA
  · exact hcol
  · exact hYi
  · exact hgeom
  · exact hphysical
  · exact hbudget
  · exact hcost
  · exact hY1
  · exact hX1
  · exact hYcap
  · exact hYi.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hcol.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hPcap
  · exact hellcap
  · exact hactivecap
  · exact hcommoncap
  · exact hquotcap
  · exact hchild

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLiveCountBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma log_eighth_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z : ℝ,1 ≤ Z → (1+Real.log Z)^8 ≤ C*Z^ε := by
  let δ := ε/8
  have hd : 0<δ := by dsimp [δ];positivity
  refine ⟨(1+1/δ)^8,by positivity,?_⟩
  intro Z hZ
  have hz : 0<Z := by linarith
  have h1 := Real.one_le_rpow hZ hd.le
  have hl := Real.log_le_rpow_div hz.le hd
  have hb : 1+Real.log Z ≤ (1+1/δ)*Z^δ := by
    calc
      _ ≤ Z^δ+Z^δ/δ := add_le_add h1 hl
      _=_ := by ring
  calc
    _ ≤ ((1+1/δ)*Z^δ)^8 := pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hb 8
    _=(1+1/δ)^8*Z^ε := by
      have he : (Z^δ)^8=Z^ε := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
        congr 1
        dsimp [δ]
        ring
      rw [mul_pow,he]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstSecondHeightCost
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstSecondHeightCost
open InverseMoment InverseAmbientProfileTower JointLogSeparation FourierBridge
open InverseMomentFirstOriginalProfile

lemma first_height_cost (degree : ℕ) (negative : Bool) (z : Frequency×(Fin 9→ℝ)) :
    (1+‖firstHeight negative z‖)^(firstDegree degree)≤
      tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2 := by
  cases negative
  · exact first_right_height_budget _ z
  · exact first_left_height_budget _ z

lemma first_weight_one_le (J : ℕ) (z : Frequency×(Fin 9→ℝ)) :
    1≤tripleHeight J z.1*coordinateHeight J z.2 := by
  simpa only [ambientWeight,tripleHeight,coordinateHeight] using ambientWeight_one_le J z

theorem second_step_first_height (degree : ℕ) (negative : Bool)
    (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hA : 0≤A) (hZ : 0≤Z)
    (z : Frequency×(Fin 9→ℝ)) :
    Czero*Z^(F+17*eta+tau+pi)+
      C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
        Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  have hw := first_weight_one_le (firstDegree degree) z
  have hh := first_height_cost degree negative z
  have hzero : Czero*Z^(F+17*eta+tau+pi)≤
      (Czero*Z^(F+17*eta+tau+pi))*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) :=
    le_mul_of_one_le_right (by positivity) hw
  have htail : Ctail*Z^(-saving)≤
      (Ctail*Z^(-saving))*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) :=
    le_mul_of_one_le_right (by positivity) hw
  have hmiddle := mul_le_mul_of_nonneg_left hh
    (show 0≤C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild) by positivity)
  have hs := add_le_add (add_le_add hzero hmiddle) htail
  convert (preTransparency := .instances) hs using 1 <;> dsimp [stepBudget] <;> ring

lemma log_fourth_small_power (Cbin ε : ℝ) (hε : 0<ε) :
    ∃ Clog : ℝ,0<Clog ∧ ∀ Z : ℝ,2≤Z→
      (1+Cbin*Real.log Z)^4≤Clog*Z^ε := by
  obtain ⟨C,hC,he⟩ := log_eighth_small_power ε hε
  let b := 1+|Cbin|
  have hb : 0<b := by dsimp [b];positivity
  refine ⟨b^4*C,mul_pos (pow_pos hb _) hC,?_⟩
  intro Z hZ
  have hZ1 : 1≤Z := by linarith
  have hl : 0≤Real.log Z := Real.log_nonneg hZ1
  have hn : |1+Cbin*Real.log Z|≤b*(1+Real.log Z) := by
    calc
      _≤1+|Cbin| *Real.log Z := by simpa [abs_mul,abs_of_nonneg hl] using abs_add_le (1:ℝ) (Cbin*Real.log Z)
      _≤_ := by dsimp [b];nlinarith [abs_nonneg Cbin]
  calc
    _ = |1+Cbin*Real.log Z|^4 := by rw [←abs_pow,abs_of_nonneg (by positivity)]
    _ ≤ (b*(1+Real.log Z))^4 := pow_le_pow_left₀ (abs_nonneg _) hn 4
    _≤b^4*(1+Real.log Z)^8 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith : 1≤1+Real.log Z) (by norm_num : 4≤8)) (by positivity)
    _≤b^4*(C*Z^ε) := mul_le_mul_of_nonneg_left (he Z hZ1) (by positivity)
    _=_ := by ring

theorem stepBudget_small_power (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0<Ctotal ∧ ∀ A Z F eta tau pi epschild saving : ℝ,
      0≤A→2≤Z→0≤eta→0≤epschild→
      -saving≤F+48*eta+tau+pi+epschild+ε→
      stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving≤
        Ctotal*(1+A)*Z^(F+48*eta+tau+pi+epschild+ε) := by
  obtain ⟨Clog,hlog,hlogs⟩ := log_fourth_small_power Cbin ε hε
  refine ⟨1+Czero+C*Clog+Ctail,by positivity,?_⟩
  intro A Z F eta tau pi epschild saving hA hZ heta hepschild hsaving
  have hZ1 : 1≤Z := by linarith
  have hZ0 : 0<Z := by linarith
  have h0 : Z^(F+17*eta+tau+pi)≤Z^(F+48*eta+tau+pi+epschild+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have h1 : C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild)≤
      C*A*Clog*Z^(F+48*eta+tau+pi+epschild+ε) := by
    calc
      _≤C*A*(Clog*Z^ε)*Z^(F+48*eta+tau+pi+epschild) := by gcongr;exact hlogs Z hZ
      _=_ := by rw [show C*A*(Clog*Z^ε)*Z^(F+48*eta+tau+pi+epschild)=
          C*A*Clog*(Z^ε*Z^(F+48*eta+tau+pi+epschild)) by ring,←Real.rpow_add hZ0];congr 1;congr 1;ring
  have h2 : Z^(-saving)≤Z^(F+48*eta+tau+pi+epschild+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 hsaving
  have hsum := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 hz) h1)
    (mul_le_mul_of_nonneg_left h2 ht)
  unfold stepBudget
  apply hsum.trans
  have hpow : 0≤Z^(F+48*eta+tau+pi+epschild+ε) := Real.rpow_nonneg hZ0.le _
  have hcoef : Czero+C*A*Clog+Ctail≤(1+Czero+C*Clog+Ctail)*(1+A) := by
    have hza : 0≤Czero*A := mul_nonneg hz hA
    have hta : 0≤Ctail*A := mul_nonneg ht hA
    have hc : 0≤C*Clog := mul_nonneg hC hlog.le
    nlinarith
  convert (preTransparency := .instances) mul_le_mul_of_nonneg_right hcoef hpow using 1 ; ring

theorem first_source_budget (degree : ℕ) (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0<Ctotal ∧ ∀ A Z F eta tau pi epschild saving : ℝ,
      0≤A→2≤Z→0≤eta→0≤epschild→
      -saving≤F+48*eta+tau+pi+epschild+ε→
      ∀(negative : Bool)(z : Frequency×(Fin 9→ℝ)),
      Czero*Z^(F+17*eta+tau+pi)+
        C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
          Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      (Ctotal*(1+A)*Z^(F+48*eta+tau+pi+epschild+ε))*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  obtain ⟨Ct,hCt,hbudget⟩ := stepBudget_small_power C Cbin Czero Ctail ε hC hz ht hε
  refine ⟨Ct,hCt,?_⟩
  intro A Z F eta tau pi epschild saving hA hZ heta heps hsaving negative z
  exact (second_step_first_height degree negative C Cbin Czero Ctail A Z F eta tau pi epschild saving
    hC hz ht hA (by linarith) z).trans
    (mul_le_mul_of_nonneg_right (hbudget A Z F eta tau pi epschild saving hA hZ heta heps hsaving)
      (le_trans zero_le_one (first_weight_one_le _ z)))

theorem first_source_requested_loss (degree : ℕ) (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0<Ctotal ∧ ∀ A Z F eta tau pi epschild saving loss : ℝ,
      0≤A→2≤Z→0≤eta→0≤epschild→
      -saving≤F+48*eta+tau+pi+epschild+ε→
      48*eta+tau+pi+epschild+ε≤loss→
      ∀(negative : Bool)(z : Frequency×(Fin 9→ℝ)),
      Czero*Z^(F+17*eta+tau+pi)+
        C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
          Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      (Ctotal*(1+A)*Z^(F+loss))*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  obtain ⟨Ct,hCt,hbudget⟩ := first_source_budget degree C Cbin Czero Ctail ε hC hz ht hε
  refine ⟨Ct,hCt,?_⟩
  intro A Z F eta tau pi epschild saving loss hA hZ heta heps hsaving hloss negative z
  apply (hbudget A Z F eta tau pi epschild saving hA hZ heta heps hsaving negative z).trans
  apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one (first_weight_one_le _ z))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end SevenEighths.InverseMomentFirstSecondHeightCost
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLiveHeightStep
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseAmbientProfileTower JointLogSeparation FourierBridge
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_first_height_oai
    (old:ℝ → ℂ)(oldb:ℝ)(hsold:∀y,old y≠0 → y≤oldb)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)(negative:Bool)
    (F tau saving window b em ed:ℝ)(hF:0≤F)(htau:0<tau)(hb:1≤b)
    (hhib:hi≤b)(hwindow: b≤Real.exp window)(hold:oldb≤Real.exp window)(hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁ ω₂:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (ω₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂:ℝ → ℂ) ∧
      tsupport (ω₁:ℝ → ℂ)⊆Set.Icc af bf ∧ tsupport (ω₂:ℝ → ℂ)⊆Set.Icc af bf ∧
    ∀degree:ℕ,∀eps:ℝ,0<eps → ∃C:ℝ,0<C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι → O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι →₀ ℕ))(labels:Finset (Ideal O))(β:Ideal O → (ι →₀ ℕ) → ℂ)
      (Ψ:O →* ℂ)(m:O)(slots:Finset σ)(lists:σ → Finset ι)(weights:σ → ι → ℂ)
      (Φ:𝓢(ℝ,ℂ))(Z M r ell V eta pi epschild A theta Kphysical loss:ℝ),
      2≤Z → 2≤Z^eta → 0≤M → M≤F →  (-eta≤ r)  → r≤F → 0≤ell → ell≤F → 0≤V → V≤F →
      0≤eta → eta≤1 → tau≤1 → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
      em*(20*(3*F+16)+30)≤pi/4 → ed*(20*(3*F+16)+30)≤pi/4 →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀u,‖Ψ u‖≤1) → (slots:Set σ).PairwiseDisjoint lists → slots.card≤K →
      (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) → 0≤A → 0≤epschild → -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+eps →
      48*eta+tau+pi+epschild+eps≤loss →
      let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource old theta (y/Z^r);
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
      ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ Kphysical),
      ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 negative Ψ m slots lists weights ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree → ∀z:Frequency×(Fin 9 → ℝ),
      (Z^(firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2) (parentWeight p k.2.1)
        negative Ψ m slots lists weights om (columnScale Z r k.1 k.2.1 negative) (InverseMomentFirstSecondHeightCost.firstHeight negative z) (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤
      (C*(1+A)*Z^(r+3*ell+V+loss))*
        (tripleHeight (InverseMomentFirstSecondHeightCost.firstDegree degree) z.1*
          coordinateHeight (InverseMomentFirstSecondHeightCost.firstDegree degree) z.2) :=by
  obtain ⟨w₁,w₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,he⟩:=actual_live_label_step
    old oldb hsold om lo hi hlo hs negative F tau saving window b em ed hF htau hb hhib hwindow hold hem hed K
  refine ⟨w₁,w₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree eps heps
  obtain ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,hstep⟩:=he degree
  obtain ⟨Ctotal,hCtotal,hbudget⟩:=InverseMomentFirstSecondHeightCost.first_source_requested_loss degree C Cbin Cz Ct eps hC hCz hCt heps
  refine ⟨Ctotal,hCtotal,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta Kphysical loss hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1
    hwin hpi hetapi hsmall hsmall' hQ hn hΨ hslots hcard hw hA hechild hsave hloss cutoff W mark S k hk hchild z
  have he':=hstep p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta (InverseMomentFirstSecondHeightCost.firstHeight negative z) Kphysical
    hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1 hwin hpi hetapi hsmall hsmall'
    hQ hn hΨ hslots hcard hw hA k hk hchild
  exact he'.trans (hbudget A Z (r+3*ell+V) eta tau pi epschild saving loss hA hZ heta hechild hsave hloss negative z)

end SevenEighths.InverseMoment

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseMoment.actual_live_first_height_oai := @OAI.SevenEighths.InverseMoment.actual_live_first_height_oai
