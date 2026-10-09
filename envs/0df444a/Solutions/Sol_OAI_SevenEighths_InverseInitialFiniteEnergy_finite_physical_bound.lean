-- Prove2me | solution 1 for OAI.SevenEighths.InverseInitialFiniteEnergy.finite_physical_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:09:01.658803+00:00
-- url     : https://prove2.me/submissions/055623a8-1976-4da1-a069-3d55e298b0a4

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Theorems.Thm_OAI_SevenEighths_InverseInitialHighFrequencyTail_original_physical_tail_rapid
import Theorems.Thm_OAI_SevenEighths_InverseInitialRetainedWindow_retained_window_bound

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.LocalProductAssembly
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

open ConcreteTraceCRT
open scoped ComplexConjugate

theorem canonicalSextic_inverse_eq_conj_on_units (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) (u : (O ⧸ P)ˣ) :
    (canonicalSextic P hgood (u : O ⧸ P))⁻¹ =
      star (canonicalSextic P hgood (u : O ⧸ P)) := by
  let χ := canonicalSextic P hgood
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hval : χ (u : O ⧸ P) ^ 6 = 1 := by
    rw [← χ.pow_apply_coe 6 u, hχ6, MulChar.one_apply_coe]
  exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hval (by decide))

end ActualEisensteinCubic

end

end OAI
end

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace
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

section

theorem finiteSquarefreeRow_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) :
    finiteSquarefreeRow P hgood S 1 = 1 := by
  classical
  unfold finiteSquarefreeRow
  apply Finset.prod_eq_one
  intro i hi
  simp

open EisensteinEmbedding ConcreteTraceCRT Complex

end

end ActualEisensteinCubic

end

end OAI
end

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

namespace ActualEisensteinCubic

section

open scoped ComplexConjugate

theorem canonicalSextic_conj_as_row_label
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (e : O) :
    star (canonicalSextic P hgood (Ideal.Quotient.mk P e)) =
      canonicalSextic P hgood (Ideal.Quotient.mk P e) *
        (canonicalSextic P hgood (Ideal.Quotient.mk P e)) ^ 4 := by
  let χ := canonicalSextic P hgood
  let x : O ⧸ P := Ideal.Quotient.mk P e
  have hconj : star (χ x) = (χ x)⁻¹ := by
    by_cases hx : IsUnit x
    · let u : (O ⧸ P)ˣ := hx.unit
      have hu : (u : O ⧸ P) = x := hx.unit_spec
      rw [← hu]
      exact (canonicalSextic_inverse_eq_conj_on_units P hgood u).symm
    · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
      simp [hzero]
  rw [hconj]
  by_cases hx : IsUnit x
  · have h6 : (χ x) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0),
        canonicalSextic_pow_six P hgood]
      exact MulChar.one_apply hx
    apply inv_eq_of_mul_eq_one_right
    calc
      χ x * (χ x * (χ x) ^ 4) = (χ x) ^ 6 := by ring
      _ = 1 := h6
  · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
    change (χ x)⁻¹ = χ x * (χ x) ^ 4
    simp [hzero]

theorem finiteSquarefreeRow_conj_as_row_label
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (e : O) :
    star (finiteSquarefreeRow P hgood S e) =
      finiteSquarefreeRow P hgood S e *
        (finiteSquarefreeRow P hgood S e) ^ 4 := by
  classical
  simp only [finiteSquarefreeRow, star_prod]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact canonicalSextic_conj_as_row_label (P i) (hgood i) e

theorem finiteSquarefreeRow_second_child
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι)
    (d e k J C v : O) :
    star (finiteSquarefreeRow P hgood S e) *
      finiteSquarefreeRow P hgood S d *
      finiteSquarefreeRow P hgood S k *
      (finiteSquarefreeRow P hgood S (J * C)) ^ 4 *
      (finiteSquarefreeRow P hgood S v) ^ 4 =
    finiteSquarefreeRow P hgood S (d * e * k) *
      (finiteSquarefreeRow P hgood S (J * C * e * v)) ^ 4 := by
  rw [finiteSquarefreeRow_conj_as_row_label P hgood S e]
  simp only [finiteSquarefreeRow_mul]
  ring

end

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
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

namespace ActualEisensteinCubic

theorem canonicalSextic_sq_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 := by
  have hP2 : (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hPgood (Ideal.Quotient.mk P q)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  have hQ2 : (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar Q hQgood (Ideal.Quotient.mk Q p)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  rw [hP2, hQ2, cubic_reciprocity_primary P Q hPgood hQgood p q hP hQ hpprimary hqprimary]

end ActualEisensteinCubic

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

theorem mask_mul (a b : O) :
    rowCoprimeMask P S (a * b) = rowCoprimeMask P S a * rowCoprimeMask P S b := by
  simp only [← row_sixth P hg S, finiteSquarefreeRow_mul, mul_pow]

theorem row_zero_of_mask_zero (a : O) (h : rowCoprimeMask P S a = 0) :
    finiteSquarefreeRow P hg S a = 0 := by
  have hq := row_sixth P hg S a
  rw [h] at hq
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hq

end Rows

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
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
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss canonicalProductGauss_cross_factors)
open MixedGaussConversion (localGauss)

theorem canonicalProductGauss_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ S, e i ≠ 0) :
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) =
      gaussBlock p hp hg S e := by
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  have hin (i : S) :
      (∏ k ∈ (Finset.univ : Finset S).erase i,
        (canonicalSextic (Ideal.span {p i.val}) (hg i.val) ^ e i.val)
          (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) =
      ∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val := by
    apply Finset.prod_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h), k.property⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro k hk
      refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h),
        Finset.mem_univ _⟩
    · intro k hk
      exact MulChar.pow_apply' _ (he i.val i.property) _
  calc
    _ = ∏ i : S, (∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val) *
        localGauss (p i.val) (hp i.val) (hg i.val) (e i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hin i]
      rfl
    _ = _ := Finset.prod_coe_sort S (fun i =>
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) * localGauss (p i) (hp i) (hg i) (e i))

theorem gaussBlock_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) :
    gaussBlock p hp hg (S ∪ T) e =
      gaussBlock p hp hg S e * gaussBlock p hp hg T e * blockCross p hg S T e := by
  have hS (i : ι) (hi : i ∈ S) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ T, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ T := fun h => Finset.disjoint_left.mp hd hi h
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hT (i : ι) (hi : i ∈ T) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ T.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ S, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ S := fun h => Finset.disjoint_left.mp hd h hi
    rw [Finset.union_comm S T, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpS : (∏ i ∈ S, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg S e * (∏ i ∈ S, ∏ k ∈ T, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hS i hi]
    ring
  have hpT : (∏ i ∈ T, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg T e * (∏ i ∈ T, ∏ k ∈ S, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hT i hi]
    ring
  rw [gaussBlock, Finset.prod_union hd, hpS, hpT,
    Finset.prod_comm (s := T) (t := S)]
  simp only [blockCross, Finset.prod_mul_distrib]
  ring

theorem columnCoefficient_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg S =
      star (FiniteGaussPhase.angularFactor (∏ i ∈ S, p i)) *
        gaussBlock p hp hg S (fun _ => 2) := by
  unfold MixedCrossSeparation.columnCoefficient FiniteGaussPhase.canonicalProductCoefficient
  rw [Finset.prod_coe_sort]
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg S (fun _ => 2) (fun _ _ => by decide)]

theorem blockCross_two_eq_row_four {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    blockCross p hg S T (fun _ => 2) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  simp only [blockCross, finiteSquarefreeRow, map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  change crossSymbol p hg i k ^ 2 * crossSymbol p hg k i ^ 2 = crossSymbol p hg i k ^ 4
  rw [← hr]
  ring

theorem columnCoefficient_union_row_four {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg (S ∪ T) =
      MixedCrossSeparation.columnCoefficient p hp hcop hg S *
        MixedCrossSeparation.columnCoefficient p hp hcop hg T *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  have ha : FiniteGaussPhase.angularFactor (∏ i ∈ S ∪ T, p i) =
      FiniteGaussPhase.angularFactor (∏ i ∈ S, p i) *
        FiniteGaussPhase.angularFactor (∏ i ∈ T, p i) := by
    rw [Finset.prod_union hd]
    simp only [FiniteGaussPhase.angularFactor, map_mul, norm_mul, Complex.ofReal_mul,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [columnCoefficient_eq_gaussBlock, columnCoefficient_eq_gaussBlock,
    columnCoefficient_eq_gaussBlock, ha, star_mul, gaussBlock_union p hp hg S T hd,
    blockCross_two_eq_row_four p hg hpr S T]
  ring

end FirstPassCubeLabels

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy
namespace OAI

noncomputable section

namespace FirstPassCubeLabels

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

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)

section Local
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i)

theorem row_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    finiteSquarefreeRow P hg (S ∪ T) a =
      finiteSquarefreeRow P hg S a * finiteSquarefreeRow P hg T a := by
  exact Finset.prod_union hd

include hg in
theorem mask_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    rowCoprimeMask P (S ∪ T) a = rowCoprimeMask P S a * rowCoprimeMask P T a := by
  simp only [← row_sixth P hg, row_union P hg S T hd, mul_pow]

end Local

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FourierBridge (logPhase)

end FirstPassCubeLabels

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage
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

namespace SecondPassArithmetic

section

open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels (row_union mask_union mask_mul)

section Masks
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem mask_star_row (e : O) :
    rowCoprimeMask P S e * star (finiteSquarefreeRow P hg S e) =
      star (finiteSquarefreeRow P hg S e) := by
  by_cases h : ∃ i ∈ S, e ∈ P i
  · have hm : rowCoprimeMask P S e = 0 := by simp [rowCoprimeMask, h]
    rw [FirstPassCubeLabels.row_zero_of_mask_zero P hg S e hm]
    simp
  · simp [rowCoprimeMask, h]

theorem second_child_masked (m r c d e k v : O) :
    rowCoprimeMask P S (m * (e * r)) *
      star (finiteSquarefreeRow P hg S e) *
      finiteSquarefreeRow P hg S d * finiteSquarefreeRow P hg S k *
      finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S v ^ 4 =
    rowCoprimeMask P S (m * r) *
      finiteSquarefreeRow P hg S (d * e * k) *
      finiteSquarefreeRow P hg S (c * e * v) ^ 4 := by
  have hr := finiteSquarefreeRow_second_child P hg S d e k c 1 v
  simp only [mul_one] at hr
  rw [mask_mul P hg S m (e * r), mask_mul P hg S e r,
    mask_mul P hg S m r]
  calc
    _ = (rowCoprimeMask P S m * rowCoprimeMask P S r) *
      (rowCoprimeMask P S e * star (finiteSquarefreeRow P hg S e)) *
      finiteSquarefreeRow P hg S d * finiteSquarefreeRow P hg S k *
      finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S v ^ 4 := by ring
    _ = _ := by
      rw [mask_star_row]
      have hh := congrArg (fun z : ℂ => (rowCoprimeMask P S m * rowCoprimeMask P S r) * z) hr
      convert (preTransparency := .instances) hh using 1 <;> ring
end Masks

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondPreColumn_union
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m r c d e k : O) (H : Finset ι → ℂ)
    (V N : Finset ι) (hd : Disjoint V N) :
    secondPreColumn p hp hcop hg Ψ (m * (e * r)) c d e k H (V ∪ N) =
      secondPreColumn p hp hcop hg Ψ (m * (e * r)) c d e k (fun _ => 1) V *
      secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
        (fun U => H (V ∪ U)) N := by
  have hA := FirstPassCubeLabels.columnCoefficient_union_row_four
    p hp hcop hg hpr N V hd.symm
  rw [Finset.union_comm N V] at hA
  have hrow := second_child_masked (fun i => Ideal.span {p i}) hg N m r c d e k (∏ i ∈ V, p i)
  simp only [secondPreColumn, secondChildColumn, hA, Finset.prod_union hd,
    map_mul, row_union _ hg V N hd, mask_union _ hg V N hd,
    mul_pow, star_mul, mul_one]
  calc
    _ = (columnCoefficient p hp hcop hg V * Ψ (∏ i ∈ V, p i) *
      rowCoprimeMask (fun i => Ideal.span {p i}) V (m * (e * r)) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V c ^ 4 *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V d *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V e) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V k) *
      (columnCoefficient p hp hcop hg N * Ψ (∏ i ∈ N, p i) *
        (rowCoprimeMask (fun i => Ideal.span {p i}) N (m * (e * r)) *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N e) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N d *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N k *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N c ^ 4 *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (∏ i ∈ V, p i) ^ 4) *
        H (V ∪ N)) := by ring
    _ = _ := by rw [hrow]; ring

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ResidualSectors
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
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

theorem rowCoprimeMask_eq_of_span_eq {ι : Type*} (P : ι → Ideal O)
    (S : Finset ι) {a b : O} (hab : Ideal.span {a} = Ideal.span {b}) :
    rowCoprimeMask P S a = rowCoprimeMask P S b := by
  have hm (i : ι) : a ∈ P i ↔ b ∈ P i := by
    rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.span_singleton_le_iff_mem, hab]
  simp only [rowCoprimeMask, hm]

theorem rowCoprimeMask_mul_eq_of_span_eq {ι : Type*} (P : ι → Ideal O)
    (S : Finset ι) (m : O) {a b : O} (hab : Ideal.span {a} = Ideal.span {b}) :
    rowCoprimeMask P S (m*a) = rowCoprimeMask P S (m*b) := by
  apply rowCoprimeMask_eq_of_span_eq P S
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton, hab]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GeneratorTransport
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildColumn_label_transfer (Ψ : Eis →* ℂ) (m a f k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ m (a*f) k H S =
      secondChildColumn p hp hcop hg Ψ m f (a^4*k) H S := by
  simp only [secondChildColumn, finiteSquarefreeRow, map_mul, map_pow,
    Finset.prod_mul_distrib, Finset.prod_pow, mul_pow]
  ring

theorem secondChildColumn_generator_unit (Ψ : Eis →* ℂ) (u : Eisˣ) (m f d k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ m ((u:Eis)*f) ((u:Eis)*d*k) H S =
      secondChildColumn p hp hcop hg Ψ m f (d*((u:Eis)^5*k)) H S := by
  rw [secondChildColumn_label_transfer]
  congr 1
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open MixedCrossSeparation (columnCoefficient)
open SevenEighths.InverseMoment SevenEighths.InverseInitialFibers
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀∉Ideal.span {p i})

theorem initialColumn_eq_secondPre (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hp hcop hg Ψ j C d h H S =
      secondPreColumn p hp hcop hg Ψ (j*C) 1 1 d h H S := by
  have hone := ActualEisensteinCubic.finiteSquarefreeRow_one (fun i=>Ideal.span {p i}) hg S
  simp only [initialColumn,secondPreColumn,hone,one_pow,mul_one]

theorem initial_common_extraction (hpr : ∀ i,λ₀^2∣p i-1)
    (Ψ : O →* ℂ) (j t d h : O) (H : Finset ι→ℂ)
    (V N : Finset ι) (hVN : Disjoint V N) :
    initialColumn p hp hcop hg Ψ j (d*t) d h H (V∪N) =
      initialColumn p hp hcop hg Ψ j (d*t) d h (fun _=>1) V *
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>H (V∪U)) N := by
  simp only [initialColumn_eq_secondPre]
  simpa only [one_mul] using secondPreColumn_union p hp hcop hg hpr Ψ j t 1 1 d h H V N hVN

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_ne_zero (S : Finset ι) : sourceIdeal p S≠0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_union (S T : Finset ι) (hst : Disjoint S T) :
    sourceIdeal p (S∪T)=sourceIdeal p S*sourceIdeal p T := by
  simp only [sourceIdeal,Finset.prod_union hst,Ideal.span_singleton_mul_span_singleton]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_dvd (E G : Finset ι) (hEG : E⊆G) : sourceIdeal p E∣sourceIdeal p G := by
  refine ⟨sourceIdeal p (G\E),?_⟩
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]

theorem initial_poisson_child_normalized
    (hpr : ∀ i,λ₀^2∣p i-1) (G E V : Finset ι) (Ψ : O →* ℂ)
    (j e t h : O) (he : Ideal.span {e}=sourceIdeal p E)
    (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Oˣ, e=(u:O)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (H : Finset ι→ℂ) (N : Finset ι),
        secondChildColumn p hp hcop hg Ψ (j*t) (e*∏ i∈V,p i) (e*h) H N =
          secondChildColumn p hp hcop hg Ψ
            (j*primaryGenerator (sourceIdeal p (G\E)))
            (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
            (primaryGenerator (sourceIdeal p E)*((u:O)^5*h)) H N := by
  have hgE : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  obtain ⟨u,hu⟩ := generator_eq_unit_primary (sourceIdeal p E) e he hgE
  refine ⟨u,hu,?_⟩
  intro H N
  have hts : Ideal.span {t}=Ideal.span {primaryGenerator (sourceIdeal p (G\E))} := by
    rw [ht,sourceIdeal_gen p hp hpr (G\E)]
    rfl
  have hmask := rowCoprimeMask_mul_eq_of_span_eq (fun i=>Ideal.span {p i}) N j hts
  have hchange : secondChildColumn p hp hcop hg Ψ (j*t) (e*∏ i∈V,p i) (e*h) H N =
      secondChildColumn p hp hcop hg Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
        (e*∏ i∈V,p i) (e*h) H N := by
    simp only [secondChildColumn,hmask]
  rw [hchange,hu,primaryGenerator_mul,sourceIdeal_gen p hp hpr V]
  rw [mul_assoc (u:O)]
  exact secondChildColumn_generator_unit p hp hcop hg Ψ u _ _ _ h H N

end SevenEighths.InverseInitialArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialKernelBridge
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open EisensteinSchwartzPoisson UniqueFactorizationMonoid CanonicalQuadraticSieve
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialOverlap
open SevenEighths.InverseInitialProfile
namespace SevenEighths.InverseInitialKernelBridge

local notation "Eis" => ActualEisensteinCubic.O
local notation "N" => fun I : Ideal Eis => (Ideal.absNorm I : ℝ)
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal Eis)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
  (hg : ∀ i, goodLambda ∉ P i)

private theorem physicalKernel_vector (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m q₀ q₁ q₂ q₃ q₄ q₅ : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m ![q₀,q₁,q₂,q₃,q₄,q₅] =
      ((Z^(-D)*Z^m/(q₁*q₂*Real.sqrt (q₄*q₅)) : ℝ) : ℂ)*
        W₁ (q₀*q₂*q₄/Z^D)*W₂ (q₀*q₂*q₅/Z^D)*
          paperRadialFourier Φ (Z^m*q₃/(q₁*q₂^2*q₄*q₅)) := rfl

theorem physicalCoordinates_pos (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (hC : C ≠ 0) (hd : d ≠ 0) (hs : s ≠ 0) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (hh : h ≠ 0) :
    ∀ i, 0 < physicalCoordinates C d s n₁ n₂ h i := by
  have hp (I : Ideal Eis) (hI : I ≠ 0) : 0 < N I := by
    change 0 < (Ideal.absNorm I : ℝ)
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hp C hC
  · exact hp d hd
  · exact hp s hs
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh))
  · exact hp n₁ h₁
  · exact hp n₂ h₂

theorem physicalKernel_common_factor (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d 1 (s*n₁) (s*n₂) h) =
      physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d s n₁ n₂ h) := by
  have hroot : Real.sqrt ((N s*N n₁)*(N s*N n₂)) = N s*Real.sqrt (N n₁*N n₂) := by
    rw [show (N s*N n₁)*(N s*N n₂) = (N s)^2*(N n₁*N n₂) from by ring_nf,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  unfold physicalCoordinates
  rw [physicalKernel_vector,physicalKernel_vector]
  simp only [map_one,Nat.cast_one,map_mul,Nat.cast_mul,mul_one,one_pow]
  rw [hroot]
  have hl : N C*(N s*N n₁)/Z^D = N C*N s*N n₁/Z^D := by ring_nf
  have hr : N C*(N s*N n₂)/Z^D = N C*N s*N n₂/Z^D := by ring_nf
  have hk : Z^m*‖eisEmbedding h‖^2/(N d*(N s*N n₁)*(N s*N n₂)) =
      Z^m*‖eisEmbedding h‖^2/(N d*(N s)^2*N n₁*N n₂) := by ring_nf
  rw [hl,hr,hk]
  push_cast
  ring_nf

open InverseInitialArithmetic SecondPassArithmetic

end SevenEighths.InverseInitialKernelBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialRayAttachment
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialRayAttachment
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialArithmetic InverseInitialProfile
local notation "O" => ActualEisensteinCubic.O

theorem poolPrimary_injective (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I) :
    Function.Injective (fun i : primePool F => Ideal.span {poolPrimary F i}) := by
  intro i k he
  change Ideal.span {poolPrimary F i} = Ideal.span {poolPrimary F k} at he
  rw [poolPrimary_span F hF,poolPrimary_span F hF] at he
  exact Subtype.ext he

end SevenEighths.InverseInitialRayAttachment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalMeasure
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace SevenEighths.InverseInitialPhysicalMeasure
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialRayAttachment
open InverseInitialKernelBridge InverseInitialProfile InverseInitialClippedColumns
open MeasureTheory FourierBridge JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem coordinates_pos (x : Point ι) (hx : Valid x) : ∀ i,0<coordinates p x i :=
  physicalCoordinates_pos _ _ _ _ _ _ (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _) hx.frequency_nonzero

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem quotient_span (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) :
    Ideal.span {quotient p x}=sourceIdeal p (x.common\x.divisor) := by
  rw [quotient,sourceIdeal_gen p hp hpr]
  rfl

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem common_span (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) (hx : Valid x) :
    Ideal.span {divisor p x*quotient p x}=sourceIdeal p x.common := by
  rw [←Ideal.span_singleton_mul_span_singleton,divisor_span p,quotient_span p hp hpr,
    ←sourceIdeal_union p _ _ (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hx.divisor_subset]

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem unitSector_spec (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) :
    divisor p x=(unitSector p hp hpr x:O)*primaryGenerator (sourceIdeal p x.divisor) :=
  Classical.choose_spec (generator_eq_unit_primary (sourceIdeal p x.divisor) (divisor p x)
    (divisor_span p x) (by rw [sourceIdeal_gen p hp hpr]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

theorem child_normalized (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι)
    (Ψ : O →* ℂ) (j h : O) (H : Finset ι→ℂ) (N : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (j*quotient p x)
      (divisor p x*∏ i∈x.overlap,p i) (divisor p x*h) H N =
    secondChildColumn p hp hcop hg Ψ (j*quotient p x)
      (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
      (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h)) H N := by
  obtain ⟨u,hu,he⟩ := initial_poisson_child_normalized p hp hcop hg hpr
    x.common x.divisor x.overlap Ψ j (divisor p x) (quotient p x) h
    (divisor_span p x) (quotient_span p hp hpr x)
  have hgen : primaryGenerator (sourceIdeal p x.divisor)≠0 := by
    rw [sourceIdeal_gen p hp hpr];exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hu' : u=unitSector p hp hpr x := Units.val_injective
    (mul_right_cancel₀ hgen (hu.symm.trans (unitSector_spec p hp hpr x)))
  simpa only [hu',quotient] using he H N

include hp hcop hg in
theorem column_extraction (hpr : ∀ i,goodLambda^2∣p i-1)
    (x : Point ι) (hx : Valid x) (Ψ : O →* ℂ) (j h : O)
    (σ : Finset ι→ℂ) (N : Finset ι) (hN : Disjoint x.overlap N) :
    initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h
      (fun A=>σ (x.common∪A)) (x.overlap∪N) =
      initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h (fun _=>1) x.overlap *
      secondChildColumn p hp hcop hg Ψ (j*quotient p x)
        (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
        (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h))
        (fun A=>σ (x.common∪(x.overlap∪A))) N := by
  have hm (A : Finset ι) :
      rowCoprimeMask (fun i=>Ideal.span {p i}) A (j*∏ i∈x.common,p i)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) A (j*(divisor p x*quotient p x)) :=
    rowCoprimeMask_mul_eq_of_span_eq _ A j (common_span p hp hpr x hx).symm
  have hc (H : Finset ι→ℂ) (A : Finset ι) :
      initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h H A =
      initialColumn p hp hcop hg Ψ j (divisor p x*quotient p x) (divisor p x) h H A := by
    simp only [initialColumn,hm]
  rw [hc,initial_common_extraction p hp hcop hg hpr Ψ j (quotient p x) (divisor p x) h _ _ _ hN,
    ←hc,child_normalized p hp hcop hg hpr]

include hp hcop hg in
theorem physicalTerm_extracted (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (x : Point ι) (hx : Valid x) (ρ : SecondRayIndex) :
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ =
      outerCoefficient p hp hcop hg Ψ j x ρ *
      star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency (fun _=>1) x.left) *
      canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency) (fun _=>1) x.right *
      physicalKernel W₁ W₂ Φ Z D m (coordinates p x) := by
  unfold physicalTerm
  rw [column_extraction p hp hcop hg hpr x hx _ _ _ σ _ hx.overlap_left,
    column_extraction p hp hcop hg hpr x hx _ _ _ σ _ hx.overlap_right,
    sourceIdeal_union p _ _ hx.overlap_left,sourceIdeal_union p _ _ hx.overlap_right,
    physicalKernel_common_factor]
  simp only [canonicalColumn,mul_one,star_mul,outerCoefficient,coordinates]
  ring

open InverseInitialOverlap InverseInitialPoissonBridge CanonicalQuadraticSieve

end SevenEighths.InverseInitialPhysicalMeasure

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSource
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialProfile
open SevenEighths.InverseInitialArithmetic SevenEighths.InverseInitialPhysicalMeasure
open SevenEighths.InverseInitialEnergyCallerModes
namespace SevenEighths.InverseInitialEnergyCallerSource
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem point_pair_injective (x : Source (ι:=ι) 0) :
    Function.Injective (fun q : Finset ι × Finset ι=>sourcePoint x q.1 q.2) := by
  intro q r h
  exact Prod.ext (congrArg Point.left h) (congrArg Point.right h)

theorem rectangles_disjoint (F : Finset ι) {x y : Source (ι:=ι) 0} (hne : x≠y) :
    Disjoint (rectangle F x) (rectangle F y) := by
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hz₁
  obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hz₂
  have he := congrArg erasePoint (hea.trans heb.symm)
  simp only [erase_sourcePoint] at he
  exact hne he

theorem pointSource_sum {A : Type*} [AddCommMonoid A]
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0)) (f : Point ι→A) :
    (∑ x∈pointSource F S,f x) =
      ∑ y∈S,∑ N∈(F\y.overlap).powerset,∑ M∈(F\y.overlap).powerset,
        f (sourcePoint y N M) := by
  rw [pointSource,Finset.sum_biUnion (fun x hx y hy hne=>rectangles_disjoint F hne)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [rectangle,Finset.sum_image (fun x _ z _ he=>point_pair_injective y he),Finset.sum_product]

theorem pointSource_valid (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hdiv : ∀ x∈S,x.divisor⊆x.common)
    (hfreq : ∀ x∈S,x.frequency≠0) : ∀ y∈pointSource F S,Valid y := by
  intro y hy
  obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hy
  have hd (U : Finset ι) (hU : U∈(F\x.overlap).powerset) : Disjoint x.overlap U := by
    apply Finset.disjoint_left.mpr
    intro i hi hiU
    exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hiU)).2 hi
  exact ⟨hdiv x hx,hd N (Finset.mem_product.mp hNM).1,
    hd M (Finset.mem_product.mp hNM).2,hfreq x hx⟩

variable {σ : Type*} [DecidableEq σ]
  (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseInitialEnergyCallerSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindows
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerSourceMask
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_windowSource
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H m:ℝ)(w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ)) :
    physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (windowSource p S ψ Z D B v θ H))
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,windowSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases ho:outerCutoff ψ (sourceRelative p x Z D B v θ H)=0
  · simp only [ho,ne_eq,not_true_eq_false,ite_false,Function.comp_apply,erase_sourcePoint,
      mul_zero,zero_mul,Finset.sum_const_zero]
  · rw [if_pos ho]

end SevenEighths.InverseInitialEnergyCallerWindows

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

theorem annulus_pos (x : ℝ) (hlo : 1/4 < x) (hhi : x < 1) : 0 < annulus x := by
  by_cases hx : x ≤ 1/2
  · rw [annulus,cutoff_one x hx]
    have h := Real.smoothTransition.lt_one_of_lt_one (by linarith : 2-2*(2*x) < 1)
    exact sub_pos.mpr h
  · rw [annulus,cutoff_zero (2*x) (by linarith),sub_zero]
    exact Real.smoothTransition.pos_of_pos (by linarith)

theorem dyadicWeight_support_eq (n : ℤ) :
    Function.support (dyadicWeight n)=Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  apply Set.Subset.antisymm (dyadicWeight_support n)
  intro q hq
  apply ne_of_gt
  apply annulus_pos
  · apply (lt_div_iff₀ (dyadicScale_pos n)).mpr
    linarith [hq.1]
  · exact (div_lt_one (dyadicScale_pos n)).mpr hq.2

theorem dyadicWeight_tsupport_eq (n : ℤ) :
    tsupport (dyadicWeight n)=Set.Icc (dyadicScale n/4) (dyadicScale n) := by
  rw [tsupport,dyadicWeight_support_eq,closure_Ioo]
  linarith [dyadicScale_pos n]

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DyadicCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.CenteredMomentDyadicCount
open CenteredMomentSectorLocalization

lemma logb_dyadicScale (n : ℤ) : Real.logb 2 (dyadicScale n)=(n:ℝ) := by
  rw [dyadicScale,←Real.rpow_intCast,Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num)]

lemma mem_indices_iff_scale (a b : ℝ) (ha : 0<a) (hb : 0<b) (n : ℤ) :
    n∈indices a b ↔ a≤dyadicScale n ∧ dyadicScale n≤4*b := by
  rw [indices,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  rw [←logb_dyadicScale n]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(Real.logb_le_logb (by norm_num) ha (dyadicScale_pos n)).mp h1,
      (Real.logb_le_logb (by norm_num) (dyadicScale_pos n) (by positivity)).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨Real.logb_le_logb_of_le (by norm_num) ha h1,
      Real.logb_le_logb_of_le (by norm_num) (dyadicScale_pos n) h2⟩

lemma mem_indices_iff_whole_support (a b : ℝ) (ha : 0<a) (hab : a≤b) (n : ℤ) :
    n∈indices a b ↔ ∃q∈Icc a b,q∈tsupport (dyadicWeight n) := by
  rw [mem_indices_iff_scale a b ha (ha.trans_le hab) n]
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨max a (dyadicScale n/4),⟨le_max_left _ _,max_le hab (by linarith)⟩,?_⟩
    rw [dyadicWeight_tsupport_eq]
    exact ⟨le_max_right _ _,max_le hlo (by linarith [dyadicScale_pos n])⟩
  · rintro ⟨q,hq,hq'⟩
    have hh := dyadicWeight_tsupport n hq'
    exact ⟨hq.1.trans hh.2,by linarith [hq.2,hh.1]⟩

lemma support_indices (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b)
    (n : ℤ) (hne : dyadicWeight n q≠0) : n∈indices a b :=
  (mem_indices_iff_whole_support a b ha (hq.1.trans hq.2) n).mpr
    ⟨q,hq,subset_tsupport _ hne⟩

lemma logb_four_mul (b : ℝ) (hb : 0<b) :
    Real.logb 2 (4*b)=2+Real.logb 2 b := by
  rw [Real.logb_mul (by norm_num) hb.ne']
  congr 1
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem indices_card_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ((indices a b).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have hb := ha.trans_le hab
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha hab
  have hu := Int.ceil_lt_add_one (Real.logb 2 a)
  have hl := Int.sub_one_lt_floor (Real.logb 2 (4*b))
  have he := logb_four_mul b hb
  have hle : ⌈Real.logb 2 a⌉≤⌊Real.logb 2 (4*b)⌋+1 := by
    have hh : (⌈Real.logb 2 a⌉:ℝ)≤(⌊Real.logb 2 (4*b)⌋:ℝ)+1 := by linarith
    exact_mod_cast hh
  have hcard := Int.card_Icc_of_le _ _ hle
  have hcard' : ((indices a b).card:ℝ)=(⌊Real.logb 2 (4*b)⌋:ℝ)+1-(⌈Real.logb 2 a⌉:ℝ) := by
    exact_mod_cast hcard
  rw [hcard',Real.logb_div hb.ne' ha.ne']
  linarith [Int.floor_le (Real.logb 2 (4*b)),Int.le_ceil (Real.logb 2 a)]

lemma dyadic_partition_on_interval (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b) :
    (∑n∈indices a b,dyadicWeight n q)=1 := by
  rw [←dyadicWeight_partition q (ha.trans_le hq.1)]
  symm
  apply tsum_eq_sum
  intro n hn
  by_contra hne
  exact hn (support_indices a b q ha hq n hne)

theorem indices_card_log_bound (C R Z a b : ℝ) (hC : 1≤C) (hR : 0≤R)
    (hZ : 1≤Z) (ha : 0<a) (hab : a≤b) (hratio : b/a≤C*Z^R) :
    ((indices a b).card:ℝ)≤
      (3+Real.logb 2 C+R/Real.log 2)*(1+Real.log Z) := by
  have hb := ha.trans_le hab
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (div_pos hb ha) hratio
  rw [Real.logb_mul hCp.ne' (Real.rpow_pos_of_pos hZp R).ne',
    Real.logb_rpow_eq_mul_logb_of_pos hZp] at hlog
  apply (indices_card_bound a b ha hab).trans
  have hc0 := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
  have hz0 := Real.log_nonneg hZ
  have hr0 : 0≤R/Real.log 2 := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hp := mul_nonneg (show 0≤3+Real.logb 2 C by linarith) hz0
  have he : R*Real.logb 2 Z=(R/Real.log 2)*Real.log Z := by unfold Real.logb;ring
  rw [he] at hlog
  nlinarith

theorem four_indices_subpower (C R ε : ℝ) (hC : 1≤C) (hR : 0≤R) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ∀a b : Fin 4→ℝ,(∀j,0<a j) → (∀j,a j≤b j) →
      (∀j,b j/a j≤C*Z^R) →
      (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤D*Z^ε := by
  let K : ℝ := 3+Real.logb 2 C+R/Real.log 2
  have hK : 0<K := by
    have hc := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
    have hr := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [K]
    linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  refine ⟨16*K^4,by positivity,?_⟩
  filter_upwards [hlog,Filter.eventually_ge_atTop (Real.exp 1),Filter.eventually_ge_atTop (1:ℝ)] with Z hlog hZexp hZ
  intro a b ha hab hratio
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hz : 1≤Real.log Z := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ)) hZexp
    simpa only [Real.log_exp] using hh
  have hp : (Real.log Z)^4≤Z^ε := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZp.le _),one_mul] using hlog
  have hcard : (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤(K*(1+Real.log Z))^4 := by
    rw [Fintype.card_pi]
    push_cast
    calc
      _ ≤ ∏j:Fin 4,K*(1+Real.log Z) := by
        apply Finset.prod_le_prod (by intros;positivity)
        intro j hj
        simpa only [Fintype.card_coe] using indices_card_log_bound C R Z (a j) (b j) hC hR hZ (ha j) (hab j) (hratio j)
      _ = _ := by simp
  calc
    _ ≤ (K*(1+Real.log Z))^4 := hcard
    _ ≤ (K*(2*Real.log Z))^4 := by gcongr;linarith
    _ = (16*K^4)*(Real.log Z)^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentDyadicCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssembly
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis" => ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseInitialKernelBridge InverseSecondChildWindows
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

theorem exponent_scale (Z:ℝ) (hZ:1<Z) (k:ℤ) :
    Z^(exponent Z k)=dyadicScale k :=
  Real.rpow_logb (by positivity) (ne_of_gt hZ) (dyadicScale_pos k)

theorem weight_partition (a b q:Fin 4→ℝ) (ha:∀i,0<a i)
    (hq:∀i,q i∈Set.Icc (a i) (b i)) :
    (∑k:Windows a b,weight (fun i=>(k i).val) q)=1 := by
  unfold weight
  rw [←Fintype.prod_sum (fun (i:Fin 4) (k:↥(indices (a i) (b i)))=>(dyadicWeight k.val (q i):ℂ))]
  have he (i:Fin 4) : (∑k:↥(indices (a i) (b i)),(dyadicWeight k.val (q i):ℂ))=1 := by
    rw [Finset.sum_coe_sort (indices (a i) (b i)) (fun k=>(dyadicWeight k (q i):ℂ))]
    exact_mod_cast dyadic_partition_on_interval (a i) (b i) (q i) (ha i) (hq i)
  simp only [he,Finset.prod_const_one]

theorem weight_eq_cutoff (Z D:ℝ) (hZ:1<Z) (k:Fin 4→ℤ) (q:Fin 6→ℝ) :
    weight k (fun i=>q (outerIndex i)) =
      outerCutoff cutoff (relativeNorm q Z D (exponent Z (k 0))
        (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))) := by
  simp [weight,Fin.prod_univ_succ,dyadicWeight,outerIndex,outerCutoff,cutoff,
    relativeNorm,secondRelativeNorm,exponent_scale Z hZ,mul_assoc]

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem source_weight_cutoff (Z D:ℝ) (hZ:1<Z) (k:Fin 4→ℤ)
    (x:Source (ι:=ι) 0) :
    weight k (sourceNorms p x)=outerCutoff cutoff
      (sourceRelative p x Z D (exponent Z (k 0)) (exponent Z (k 2))
        (exponent Z (k 1)) (exponent Z (k 3))) :=
  weight_eq_cutoff Z D hZ k _

omit [DecidableEq ι] in
theorem sourceNorms_one_le (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal] (x:Source (ι:=ι) 0)
    (hf:x.frequency≠0) : ∀i,1≤ sourceNorms p x i := by
  have hi (I:Ideal Eis) (hI:I≠0) : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · change 1≤‖ConcreteTraceCRT.eisEmbedding x.frequency‖^2
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hi _ (by change Ideal.span {x.frequency}≠⊥; exact Ideal.span_singleton_eq_bot.not.mpr hf)

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*weight (fun i=>(k i).val) (sourceNorms p x))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨s,hsS,hx⟩:=Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩:=Finset.mem_image.mp hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Function.comp_apply,erase_sourcePoint]
  rw [←Finset.sum_mul,←Finset.mul_sum,weight_partition a b _ ha (hs s hsS),mul_one]

theorem physicalBlock_window_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,physicalBlock p hp hcop hg
      (pointSource pool (windowSource p S cutoff Z D
        (exponent Z (k 0).val) (exponent Z (k 2).val)
        (exponent Z (k 1).val) (exponent Z (k 3).val)))
      ((fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D
        (exponent Z (k 0).val) (exponent Z (k 2).val)
        (exponent Z (k 1).val) (exponent Z (k 3).val)))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  rw [physicalBlock_partition p hp hcop hg pool S a b ha hs]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [source_weight_cutoff p Z D hZ]
  exact physicalBlock_windowSource p hp hcop hg pool S cutoff Z D _ _ _ _ m w Ψ j marks W₁ W₂ Φ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyBounds
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

theorem windows_card_subpower (C R ε:ℝ)(hC:1≤C)(hR:0≤R)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀a b:Fin 4→ℝ,(∀i,0<a i)→(∀i,a i≤b i)→(∀i,b i/a i≤C*Z^R)→
        (Fintype.card (Windows a b):ℝ)≤A*Z^ε :=
  four_indices_subpower C R ε hC hR hε

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyLive
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_cap_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (cappedSource p S a b))
      (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,cappedSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hb:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)
  · rw [if_pos hb]
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    simp only [Function.comp_apply,erase_sourcePoint]
    by_contra hn
    exact hb (hcap x hx N hN M hM ρ hn)

theorem physicalBlock_live_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_window_partition p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialRetainedSupport
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialRetainedSupport
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialKernelBridge SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,goodLambda∉Ideal.span {p i})

theorem live_cutoffs (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m:ℝ)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    W₁ (coordinates p x 0*coordinates p x 2*coordinates p x 4/Z^D)≠0 ∧
    W₂ (coordinates p x 0*coordinates p x 2*coordinates p x 5/Z^D)≠0 := by
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ] at hne
  have hk:= (mul_ne_zero_iff.mp hne).2
  unfold physicalKernel at hk
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).1).2,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).2⟩

theorem live_whole_columns (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0<Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0*coordinates p x 2*coordinates p x 4≤b*Z^D ∧
    coordinates p x 0*coordinates p x 2*coordinates p x 5≤b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_cutoffs p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ hne
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₁ h₁),
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₂ h₂)⟩

include hp in
omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
theorem ideal_coordinates_one (x:Point ι):
    1≤ coordinates p x 0 ∧ 1≤ coordinates p x 1 ∧ 1≤ coordinates p x 2 ∧
    1≤ coordinates p x 4 ∧ 1≤ coordinates p x 5 := by
  have hi (S:Finset ι):(1:ℝ)≤((sourceIdeal p S).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp S))
  exact ⟨hi _,hi _,hi _,hi _,hi _⟩

theorem live_ideal_caps (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0<Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0≤b*Z^D ∧ coordinates p x 1≤b*Z^D ∧
    coordinates p x 2≤b*Z^D ∧ coordinates p x 4≤b*Z^D ∧
    coordinates p x 5≤b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_whole_columns p hp hcop hg hpr Ψ j σ W₁ W₂ Φ
    Z D m b hZ hs₁ hs₂ x hx ρ hne
  obtain ⟨hC,hd,hs,hn₁,hn₂⟩:=ideal_coordinates_one p hp x
  have hpair:1≤ coordinates p x 0*coordinates p x 2:=by nlinarith
  have hcp:coordinates p x 0≤ coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_right (by linarith) hs
  have hsp:coordinates p x 2≤ coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_left (by linarith) hC
  have hbig:coordinates p x 0*coordinates p x 2≤b*Z^D:=
    (le_mul_of_one_le_right (by positivity) hn₁).trans h₁
  have hdiv:coordinates p x 1≤ coordinates p x 0:=by
    change ((sourceIdeal p x.divisor).absNorm:ℝ)≤(sourceIdeal p x.common).absNorm
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)))
      (map_dvd Ideal.absNorm (sourceIdeal_dvd p _ _ hx.divisor_subset))
  exact ⟨hcp.trans hbig,hdiv.trans (hcp.trans hbig),hsp.trans hbig,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₁,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₂⟩

end SevenEighths.InverseInitialRetainedSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblySourceCaps
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseInitialKernelBridge InverseSecondChildWindows

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem sourceNorms_fresh (x:Source (ι:=ι) 0)(N M:Finset ι)(i:Fin 4) :
    sourceNorms p x i=coordinates p (sourcePoint x N M) (outerIndex i) := by
  fin_cases i <;> simp only [sourceNorms,coordinates,sourcePoint,physicalCoordinates,
    outerIndex,Fin.castLE,Matrix.cons_val_zero',Matrix.cons_val_succ']

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_live_caps
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T:ℝ)(hZ:0<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T)
    (x:Source (ι:=ι) 0)(hx:x∈S)(N:Finset ι)(hN:N∈(pool\x.overlap).powerset)
    (M:Finset ι)(hM:M∈(pool\x.overlap).powerset)(ρ:SecondRayIndex)
    (hn:w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m (sourcePoint x N M) ρ≠0) :
    ∀i,sourceNorms p x i∈Set.Icc 1 (physicalCaps b Z D T i) := by
  have hpnt:sourcePoint x N M∈pointSource pool S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    exact Finset.mem_image.mpr ⟨(N,M),Finset.mem_product.mpr ⟨hN,hM⟩,rfl⟩
  have hv:=pointSource_valid pool S hdiv hf _ hpnt
  have hc:=InverseInitialRetainedSupport.live_ideal_caps p hp hcop hg hpr Ψ j marks W₁ W₂ Φ
    Z D m b hZ hW₁ hW₂ (sourcePoint x N M) hv ρ (mul_ne_zero_iff.mp hn).2
  intro i
  refine ⟨sourceNorms_one_le p hp x (hf x hx) i,?_⟩
  fin_cases i
  · change sourceNorms p x 0≤b*Z^D
    rw [sourceNorms_fresh p x N M 0]
    exact hc.1
  · change sourceNorms p x 1≤b*Z^D
    rw [sourceNorms_fresh p x N M 1]
    exact hc.2.1
  · change sourceNorms p x 2≤b*Z^D
    rw [sourceNorms_fresh p x N M 2]
    exact hc.2.2.1
  · exact hT x hx

theorem actual_physical_partition
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T:ℝ)(hZ:1<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows (fun _=>1) (physicalCaps b Z D T),
      windowBlock p hp hcop hg pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T))
        w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  exact physicalBlock_live_partition p hp hcop hg pool S (fun _=>1) (physicalCaps b Z D T)
    (by intro i; norm_num) w Ψ j marks W₁ W₂ Φ Z D m hZ
    (actual_live_caps p hp hcop hg hpr pool S hdiv hf w Ψ j marks W₁ W₂ Φ Z D m b T
      (by linarith) hW₁ hW₂ hT)

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyWindows
namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff
namespace SevenEighths.InverseInitialDyadicAssembly
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

theorem cutoff_norm_le (i:Fin 4)(x:ℝ) : ‖cutoff i x‖≤1 := by
  simpa only [cutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (annulus_bounds x).1] using (annulus_bounds x).2

theorem cutoff_support (i:Fin 4) :
    Function.support (cutoff i)⊆Set.Ioo (1/4:ℝ) 1 := by
  intro x hx
  have hn:annulus x≠0 := by simpa only [Function.mem_support,cutoff,ne_eq,Complex.ofReal_eq_zero] using hx
  exact ⟨lt_of_not_ge (fun h=>hn (annulus_zero_low x h)),
    lt_of_not_ge (fun h=>hn (annulus_zero_high x h))⟩

theorem window_exponent_nonneg (Z b:ℝ)(hZ:1<Z)(hb:0<b)
    (k:ℤ)(hk:k∈indices 1 b) : 0≤exponent Z k := by
  have hs:1≤dyadicScale k := ((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).1
  exact Real.logb_nonneg hZ hs

theorem window_exponent_eventual_upper (C η:ℝ)(_hC:0<C)(hη:0<η) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(b R:ℝ),0<b→b≤C*Z^R→
      ∀k:ℤ,k∈indices 1 b→exponent Z k∈Set.Icc 0 (R+η) := by
  have ht:∀ᶠZ:ℝ in atTop,4*C≤Z^η :=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (4*C))
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro b R hb hbR k hk
  refine ⟨window_exponent_nonneg Z b hZ hb k hk,?_⟩
  have hs:=((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).2
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [exponent_scale Z hZ,Real.rpow_add (by positivity)]
  calc
    dyadicScale k≤4*b:=hs
    _≤4*(C*Z^R):=mul_le_mul_of_nonneg_left hbR (by norm_num)
    _=(4*C)*Z^R:=by ring
    _≤Z^η*Z^R:=mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (by positivity) _)
    _=Z^R*Z^η:=mul_comm _ _

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyRetained
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicAssembly
open InverseInitialProfile CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

theorem window_sum_split (a b:Fin 4→ℝ)(Z D m L:ℝ)(f:Windows a b→ℂ) :
    (∑k,f k)=(∑k∈retainedWindows a b Z D m L,f k)+
      ∑k∈tailWindows a b Z D m L,f k := by
  simpa only [retainedWindows,tailWindows,not_le] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ:Finset (Windows a b))
      (fun k=>radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D
        (exponent Z (k 0).val)≤L) f).symm

theorem retained_exponents_eventually (b R Λ:ℝ)(hb:0<b)(hR:0≤R)(hΛ:0≤Λ) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀D m L T:ℝ,D≤R→0≤ m→L≤Λ→0<T→
      ∀k∈retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L,
        ∀i,exponent Z (k i).val∈Set.Icc 0 (3*R+Λ+1) := by
  filter_upwards [window_exponent_eventual_upper b 1 hb (by norm_num)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro D m L T hD hm hL hT k hk
  have hs:radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D
      (exponent Z (k 0).val)≤L := (Finset.mem_filter.mp hk).2
  have hp:0<b*Z^D := mul_pos hb (Real.rpow_pos_of_pos (by linarith [hZ.1]) D)
  have h0:=hZ.2 (b*Z^D) D hp le_rfl (k 0).val (k 0).property
  have h1:=hZ.2 (b*Z^D) D hp le_rfl (k 1).val (k 1).property
  have h2:=hZ.2 (b*Z^D) D hp le_rfl (k 2).val (k 2).property
  have h3:=window_exponent_nonneg Z T hZ.1 hT (k 3).val (k 3).property
  unfold radialCenter at hs
  intro i
  fin_cases i
  · change exponent Z (k 0).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h0.1,by linarith [h0.2]⟩
  · change exponent Z (k 1).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h1.1,by linarith [h1.2]⟩
  · change exponent Z (k 2).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h2.1,by linarith [h2.2]⟩
  · change exponent Z (k 3).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h3,by linarith [h0.1,h1.2]⟩

theorem retained_card_of_exponents (a b:Fin 4→ℝ)(Z D m L A:ℝ)(hZ:1<Z)
    (he:∀k∈retainedWindows a b Z D m L,∀i,exponent Z (k i).val∈Set.Icc 0 A) :
    (retainedWindows a b Z D m L).card≤
      Fintype.card (Windows (fun _=>1) (fun _=>Z^A)) := by
  have hZp:0<Z := by linarith
  let f:↥(retainedWindows a b Z D m L)→Windows (fun _=>1) (fun _=>Z^A) :=
    fun k i=>⟨(k.val i).val,(mem_indices_iff_scale 1 (Z^A) (by norm_num)
      (Real.rpow_pos_of_pos hZp A) (k.val i).val).mpr ⟨by
        rw [←exponent_scale Z hZ]
        simpa only [Real.rpow_zero] using
          (Real.rpow_le_rpow_left_iff hZ).mpr (he k.val k.property i).1,by
        have hh:(dyadicScale (k.val i).val)≤Z^A := by
          rw [←exponent_scale Z hZ]
          exact (Real.rpow_le_rpow_left_iff hZ).mpr (he k.val k.property i).2
        exact hh.trans (by nlinarith [Real.rpow_pos_of_pos hZp A])⟩⟩
  have hf:Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    simpa only [f] using congrArg Subtype.val (congrFun h i)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem retained_card_subpower (b R Λ ε:ℝ)(hb:0<b)(hR:0≤R)(hΛ:0≤Λ)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in atTop,
      ∀D m L T:ℝ,D≤R→0≤ m→L≤Λ→0<T→
        ((retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L).card:ℝ)≤A*Z^ε := by
  obtain ⟨A,hA,hcount⟩:=windows_card_subpower 1 (3*R+Λ+1) ε (by norm_num) (by positivity) hε
  refine ⟨A,hA,?_⟩
  filter_upwards [retained_exponents_eventually b R Λ hb hR hΛ,hcount] with Z hz hc
  intro D m L T hD hm hL hT
  have he:=hz.2 D m L T hD hm hL hT
  have hi:=retained_card_of_exponents (fun _=>1) (physicalCaps b Z D T) Z D m L
    (3*R+Λ+1) hz.1 he
  have hp:(1:ℝ)≤Z^(3*R+Λ+1) := Real.one_le_rpow (le_of_lt hz.1) (by positivity)
  exact (by exact_mod_cast hi :
    ((retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L).card:ℝ)≤
      (Fintype.card (Windows (fun _=>1) (fun _=>Z^(3*R+Λ+1))):ℝ)).trans
    (hc (fun _=>1) (fun _=>Z^(3*R+Λ+1)) (by intro i; norm_num)
      (fun _=>hp) (by intro i; simp))

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyTail
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

theorem windowMass_cast {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) :
    (windowMass F q:ℂ)=∑k∈F,weight (fun i=>(k i).val) q := by
  simp only [windowMass,weight,Complex.ofReal_sum,Complex.ofReal_prod]

theorem windowMass_nonneg {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) :
    0≤windowMass F q := by
  apply Finset.sum_nonneg
  intro k hk
  exact Finset.prod_nonneg (fun i hi=>(dyadicWeight_bounds (k i).val (q i)).1)

theorem windowMass_univ (a b q:Fin 4→ℝ)(ha:∀i,0<a i)
    (hq:∀i,q i∈Set.Icc (a i) (b i)) :
    windowMass (Finset.univ:Finset (Windows a b)) q=1 := by
  apply Complex.ofReal_injective
  rw [windowMass_cast,Complex.ofReal_one]
  exact weight_partition a b q ha hq

theorem windowMass_le_one {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (ha:∀i,0<a i)(hq:∀i,q i∈Set.Icc (a i) (b i)) : windowMass F q≤1 := by
  rw [←windowMass_univ a b q ha hq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun k hk hnot=>Finset.prod_nonneg (fun i hi=>(dyadicWeight_bounds (k i).val (q i)).1))

theorem windowMass_norm_le_one {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (ha:∀i,0<a i)(hq:∀i,q i∈Set.Icc (a i) (b i)) : ‖(windowMass F q:ℂ)‖≤1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (windowMass_nonneg F q)]
    using windowMass_le_one F q ha hq

theorem windowMass_ne_zero_exists {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (h:windowMass F q≠0) : ∃k∈F,weight (fun i=>(k i).val) q≠0 := by
  have hc:(windowMass F q:ℂ)≠0:=by exact_mod_cast h
  rw [windowMass_cast] at hc
  exact Finset.exists_ne_zero_of_sum_ne_zero hc

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem windowBlock_eq_full
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)(k:Fin 4→ℤ) :
    windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m k =
      physicalBlock p hp hcop hg (pointSource pool S)
        ((fun x=>w x*weight k (sourceNorms p x))∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  simp_rw [source_weight_cutoff p Z D hZ]
  exact (physicalBlock_windowSource p hp hcop hg pool S cutoff Z D _ _ _ _ m
    w Ψ j marks W₁ W₂ Φ).symm

theorem sum_windowBlock_eq_mass
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z) :
    (∑k∈F,windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)) =
      physicalBlock p hp hcop hg (pointSource pool S)
        ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
        Ψ j marks W₁ W₂ Φ Z D m := by
  simp_rw [windowBlock_eq_full p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m hZ]
  unfold physicalBlock
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Function.comp_apply]
  rw [←Finset.sum_mul,←Finset.mul_sum,←windowMass_cast]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem mass_weight_bound
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(x:Source (ι:=ι) 0)
    (hx:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    ‖w x*(windowMass F (sourceNorms p x):ℂ)‖≤‖w x‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (windowMass_norm_le_one F _ ha hx)

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem tail_mass_live_bounds (a b:Fin 4→ℝ)(Z D m L:ℝ)(hZ:1<Z)
    (x:Source (ι:=ι) 0)
    (hn:windowMass (tailWindows a b Z D m L) (sourceNorms p x)≠0) :
    ∃k∈tailWindows a b Z D m L,
      L< radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D (exponent Z (k 0).val) ∧
      ∀i,sourceNorms p x i∈Set.Ioo (Z^(exponent Z (k i).val)/4) (Z^(exponent Z (k i).val)) := by
  obtain ⟨k,hk,hne⟩:=windowMass_ne_zero_exists _ _ hn
  refine ⟨k,hk,(Finset.mem_filter.mp hk).2,?_⟩
  intro i
  have hi:(dyadicWeight (k i).val (sourceNorms p x i):ℂ)≠0 :=
    Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
  have hr:dyadicWeight (k i).val (sourceNorms p x i)≠0 := by exact_mod_cast hi
  rw [exponent_scale Z hZ]
  exact dyadicWeight_support (k i).val hr

theorem physicalBlock_filter_of_live
    (source:Finset (Point ι))(P:Point ι→Prop)(w:Point ι→ℂ)
    (Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hP:∀x∈source,∀ρ:SecondRayIndex,
      w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m x ρ≠0→P x) :
    physicalBlock p hp hcop hg source w Ψ j marks W₁ W₂ Φ Z D m =
      physicalBlock p hp hcop hg (source.filter P) w Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hh:P x
  · rw [if_pos hh]
  · rw [if_neg hh]
    apply Finset.sum_eq_zero
    intro ρ hρ
    by_contra hn
    exact hh (hP x hx ρ hn)

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem exists_source_frequency_cap (S:Finset (Source (ι:=ι) 0)) :
    ∃T:ℝ,0<T ∧ ∀x∈S,sourceNorms p x 3≤T := by
  have hn (x:Source (ι:=ι) 0) : 0≤ sourceNorms p x 3 := by
    change 0≤‖ConcreteTraceCRT.eisEmbedding x.frequency‖^2
    positivity
  have hs:0≤∑x∈S,sourceNorms p x 3:=Finset.sum_nonneg (fun x hx=>hn x)
  refine ⟨1+∑x∈S,sourceNorms p x 3,by linarith,?_⟩
  intro x hx
  have he:sourceNorms p x 3≤∑y∈S,sourceNorms p y 3 :=
    Finset.single_le_sum (fun y hy=>hn y) hx
  linarith

theorem actual_physical_retained_tail
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T L:ℝ)(hZ:1<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    (∑k∈retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L,
      windowBlock p hp hcop hg pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T))
        w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)) +
    physicalBlock p hp hcop hg
      (pointSource pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T)))
      ((fun x=>w x*(windowMass (tailWindows (fun _=>1) (physicalCaps b Z D T) Z D m L)
        (sourceNorms p x):ℂ))∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  rw [actual_physical_partition p hp hcop hg hpr pool S hdiv hf w Ψ j marks W₁ W₂ Φ
    Z D m b T hZ hW₁ hW₂ hT]
  rw [window_sum_split (fun _=>1) (physicalCaps b Z D T) Z D m L]
  congr 1
  exact sum_windowBlock_eq_mass p hp hcop hg pool
    (cappedSource p S (fun _=>1) (physicalCaps b Z D T)) _ _ _ w Ψ j marks W₁ W₂ Φ Z D m hZ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailKernel
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialProfile
local notation "O" => ActualEisensteinCubic.O

theorem correlated_scale_lower (Y C d v n₁ n₂ L : ℝ)
    (hY : 0<Y) (hC : 0<C) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂) (hL : 0<L)
    (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L) :
    Y*C ^2/(d*L^2) ≤ Y/(d*v^2*n₁*n₂) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul h₁ h₂ (by positivity) hL.le
  nlinarith [mul_le_mul_of_nonneg_left hh (show 0≤Y*d by positivity)]

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailAnnulus
namespace OAI

noncomputable section

namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialProfile

theorem actual_annulus_radial_lower
    (Z D m B θ H b C d v n₁ n₂ hnorm : ℝ)
    (hZ : 0<Z) (hb : 0<b) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hC : Z^B/4≤C) (hdiv : d≤Z^θ) (hfreq : Z^H/4≤hnorm)
    (h₁ : C*v*n₁≤b*Z^D) (h₂ : C*v*n₂≤b*Z^D) :
    Z^(radialCenter m H θ D B)/(64*b^2) ≤
      (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hc : 0<C := (show 0<Z^B/4 by positivity).trans_le hC
  have hh : 0≤hnorm := (show 0≤Z^H/4 by positivity).trans hfreq
  have hscale := correlated_scale_lower (Z^m) C d v n₁ n₂ (b*Z^D)
    (by positivity) hc hd hv hn₁ hn₂ (by positivity) h₁ h₂
  have he : Z^m*(Z^B)^2*Z^H/(Z^θ*(Z^D)^2)=Z^(radialCenter m H θ D B) := by
    simp only [pow_two]
    rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
      ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
    congr 1
    unfold radialCenter
    ring
  calc
    _ = Z^m*(Z^B/4)^2*(Z^H/4)/(Z^θ*(b*Z^D)^2) := by
      rw [←he]
      ring
    _ ≤ Z^m*C ^2*hnorm/(d*(b*Z^D)^2) := by gcongr
    _ = (Z^m*C ^2/(d*(b*Z^D)^2))*hnorm := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hh

theorem actual_annulus_high_gate
    (Z D m B θ H η τ b C d v n₁ n₂ hnorm : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hb : 0<b) (hd : 0<d) (hv : 0<v)
    (hn₁ : 0<n₁) (hn₂ : 0<n₂)
    (hC : Z^B/4≤C) (hdiv : d≤Z^θ) (hfreq : Z^H/4≤hnorm)
    (h₁ : C*v*n₁≤b*Z^D) (h₂ : C*v*n₂≤b*Z^D)
    (hfixed : 64*b^2≤Z^η) (hhigh : 4*η+τ≤ radialCenter m H θ D B) :
    Z^τ≤(Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  apply le_trans _ (actual_annulus_radial_lower Z D m B θ H b C d v n₁ n₂ hnorm
    hz hb hd hv hn₁ hn₂ hC hdiv hfreq h₁ h₂)
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    Z^τ*(64*b^2)≤Z^τ*Z^η := mul_le_mul_of_nonneg_left hfixed (by positivity)
    _ = Z^(τ+η) := (Real.rpow_add hz τ η).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDyadicTailGates
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicTailBound
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialDyadicAssembly InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem pointSource_erase_mem (pool : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (x : Point ι) (hx : x∈pointSource pool S) : erasePoint x∈S := by
  obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  simpa only [erase_sourcePoint] using hy

theorem pointSource_supports (pool : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hC : ∀x∈S,x.common⊆pool) (hV : ∀x∈S,x.overlap⊆pool)
    (hdiv : ∀x∈S,x.divisor⊆x.common)
    (x : Point ι) (hx : x∈pointSource pool S) :
    ∀i,InverseInitialHighFrequencyTail.sourceKey x i⊆pool := by
  obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  intro i
  fin_cases i
  · exact hC y hy
  · exact (hdiv y hy).trans (hC y hy)
  · exact hV y hy
  · exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).1).trans Finset.sdiff_subset
  · exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).2).trans Finset.sdiff_subset

omit [DecidableEq ι] in
theorem sourceKey_norm_coordinate (p : ι→O) (x : Point ι) (i : Fin 5) :
    primeProductNorm p (InverseInitialHighFrequencyTail.sourceKey x i)=coordinates p x (idealIndex i) := by
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  fin_cases i <;> simp [InverseInitialHighFrequencyTail.sourceKey,coordinates,physicalCoordinates,idealIndex,hn]

omit [DecidableEq ι] in
theorem sourceNorms_erase (p : ι→O) (x : Point ι) (i : Fin 4) :
    sourceNorms p (erasePoint x) i=coordinates p x (InverseSecondChildWindows.outerIndex i) := by
  have he : InverseInitialEnergyCallerModes.sourcePoint (erasePoint x) x.left x.right=x := by
    cases x
    rfl
  simpa only [he] using sourceNorms_fresh p (erasePoint x) x.left x.right i

omit [DecidableEq ι] in
theorem live_mass_radial_gate
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (a b : Fin 4→ℝ) (Z D m η τ bW : ℝ) (hZ : 1<Z) (hη : 0≤η)
    (hbW : 0<bW) (hfixed : 64*bW^2≤Z^η)
    (x : Point ι) (hx : Valid x)
    (hleft : coordinates p x 0*coordinates p x 2*coordinates p x 4≤bW*Z^D)
    (hright : coordinates p x 0*coordinates p x 2*coordinates p x 5≤bW*Z^D)
    (hmass : windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p (erasePoint x))≠0) :
    Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2 := by
  obtain ⟨k,hk,hhigh,hbounds⟩ := tail_mass_live_bounds p a b Z D m (4*η+τ) hZ (erasePoint x) hmass
  have hc := coordinates_pos p hp x hx
  have h₀ := (hbounds 0).1.le
  have h₁ := (hbounds 1).2.le
  have h₃ := (hbounds 3).1.le
  rw [sourceNorms_erase] at h₀ h₁ h₃
  have hh := InverseInitialHighFrequencyTail.actual_annulus_high_gate Z D m
    (exponent Z (k 0).val) (exponent Z (k 1).val) (exponent Z (k 3).val) η τ bW
    (coordinates p x 0) (coordinates p x 1) (coordinates p x 2)
    (coordinates p x 4) (coordinates p x 5) (coordinates p x 3)
    hZ.le hη hbW (hc 1) (hc 2) (hc 4) (hc 5) h₀ h₁ h₃ hleft hright hfixed hhigh.le
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  simpa [coordinates,physicalCoordinates,hn] using hh

end SevenEighths.InverseInitialDyadicTailBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDyadicTailBound
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicTailBound
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialDyadicAssembly InverseInitialProfile
open InverseInitialRetainedSupport InverseInitialHighFrequencyTail
local notation "O"=>ActualEisensteinCubic.O

theorem actual_high_mass_tail (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (weights : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖weights i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m η bW Γ B₁ B₂ : ℝ),
    1<Z → 0≤η → 0<bW → 64*bW^2≤Z^η →
    0≤Lcap → bW*Z^D≤Z^Lcap → -m≤Lcap → m-D≤Lcap →
    0≤Γ → 0≤B₁ → 0≤B₂ → (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    Function.support W₁⊆Set.Iic bW → Function.support W₂⊆Set.Iic bW →
    ∀ (pool : Finset ι) (S : Finset (Source (ι:=ι) 0)) (w : Source (ι:=ι) 0→ℂ),
    (∀x∈S,x.common⊆pool) → (∀x∈S,x.overlap⊆pool) →
    (∀x∈S,x.divisor⊆x.common) → (∀x∈S,x.frequency≠0) → (∀x∈S,‖w x‖≤Γ) →
    ∀ (a b : Fin 4→ℝ), (∀i,0<a i) → (∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) →
    ‖physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨s,C,hC,hrapid⟩ := original_physical_tail_rapid Lcap saving τ hτ
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc hpr Ψ hΨ j slots lists weights hdis hwgt W₁ W₂ Φ
    Z D m η bW Γ B₁ B₂ hZ hη hbW hfixed hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ hs₁ hs₂
    pool S w hcommon hoverlap hdiv hfreq hw a b ha hrange
  let wt : Point ι→ℂ := ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ))
    (sourceNorms p x):ℂ))∘erasePoint)
  let live (x : Point ι) : Prop := ∃ρ : SecondRayIndex,
    wt x*physicalTerm p hp hcop hg Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m x ρ≠0
  let F := (pointSource pool S).filter live
  have hmem (x) (hx : x∈F) : x∈pointSource pool S := (Finset.mem_filter.mp hx).1
  have hvalid (x) (hx : x∈F) : Valid x := pointSource_valid pool S hdiv hfreq x (hmem x hx)
  have hold (x) (hx : x∈F) : erasePoint x∈S := pointSource_erase_mem pool S x (hmem x hx)
  have hgeometry (x) (hx : x∈F) :
      (coordinates p x 0≤bW*Z^D ∧ coordinates p x 1≤bW*Z^D ∧
       coordinates p x 2≤bW*Z^D ∧ coordinates p x 4≤bW*Z^D ∧ coordinates p x 5≤bW*Z^D) ∧
      (coordinates p x 0*coordinates p x 2*coordinates p x 4≤bW*Z^D ∧
       coordinates p x 0*coordinates p x 2*coordinates p x 5≤bW*Z^D) ∧
      windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p (erasePoint x))≠0 := by
    obtain ⟨ρ,hρ⟩ := (Finset.mem_filter.mp hx).2
    have hpterm := (mul_ne_zero_iff.mp hρ).2
    refine ⟨live_ideal_caps p hp hcop hg hpr Ψ j _ W₁ W₂ Φ Z D m bW
      (by linarith) hs₁ hs₂ x (hvalid x hx) ρ hpterm,
      live_whole_columns p hp hcop hg hpr Ψ j _ W₁ W₂ Φ Z D m bW
      (by linarith) hs₁ hs₂ x (hvalid x hx) ρ hpterm,?_⟩
    intro hz
    apply (mul_ne_zero_iff.mp hρ).1
    simp only [wt,Function.comp_apply,hz,Complex.ofReal_zero,mul_zero]
  have hn (x : Point ι) (i : Fin 5) := sourceKey_norm_coordinate p x i
  have hwhole (x) (hx : x∈F) :
      primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤bW*Z^D ∧
      primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤bW*Z^D := by
    have he := (hgeometry x hx).2.1
    have hn0 := hn x 0
    have hn2 := hn x 2
    have hn3 := hn x 3
    have hn4 := hn x 4
    simp [sourceKey,idealIndex] at hn0 hn2 hn3 hn4
    rw [←hn0,←hn2,←hn3,←hn4] at he
    exact he
  have hfilter := physicalBlock_filter_of_live p hp hcop hg (pointSource pool S) live wt Ψ j
    (primeMark slots lists weights) W₁ W₂ Φ Z D m (fun x hx ρ hn=>⟨ρ,hn⟩)
  change ‖physicalBlock p hp hcop hg (pointSource pool S) wt Ψ j _ W₁ W₂ Φ Z D m‖≤_
  rw [hfilter]
  have hr := hrapid p hp hcop hg hinj hc Ψ hΨ j slots lists weights hdis hwgt W₁ W₂ Φ
    Z D m (max 1 (bW*Z^D)) Γ B₁ B₂ hZ.le (le_max_left _ _) hcap
    (max_le (Real.one_le_rpow hZ.le hcap) hsize) hm hmd hΓ hB₁ hB₂ hW₁ hW₂ pool F wt hvalid
  suffices hbound : ‖physicalBlock p hp hcop hg F wt Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) by
    have hset : @Finset.filter (Point ι) live (fun x=>Classical.propDecidable (live x))
        (pointSource pool S)=F := by
      ext x
      simp only [Finset.mem_filter,F]
    rw [hset]
    exact hbound
  refine hr ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact (mass_weight_bound p a b _ ha w (erasePoint x) (hrange _ (hold x hx))).trans (hw _ (hold x hx))
  · intro x hx
    exact pointSource_supports pool S hcommon hoverlap hdiv x (hmem x hx)
  · intro x hx i
    rw [sourceKey_norm_coordinate]
    have he := (hgeometry x hx).1
    apply le_trans _ (le_max_right 1 (bW*Z^D))
    fin_cases i
    · exact he.1
    · exact he.2.1
    · exact he.2.2.1
    · exact he.2.2.2.1
    · exact he.2.2.2.2
  · intro x hx
    exact (hwhole x hx).1.trans (le_max_right _ _)
  · intro x hx
    exact (hwhole x hx).2.trans (le_max_right _ _)
  · intro x hx
    exact live_mass_radial_gate p hp a b Z D m η τ bW hZ hη hbW hfixed x
      (hvalid x hx) (hgeometry x hx).2.1.1 (hgeometry x hx).2.1.2 (hgeometry x hx).2.2

end SevenEighths.InverseInitialDyadicTailBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialProfileBounds
namespace OAI

noncomputable section

open scoped Classical SchwartzMap
namespace SevenEighths.InverseInitialProfileBounds
open InverseInitialProfile InverseMoment FourierBridge

theorem clipped_norm (W:ℝ→ℂ)(c θ x:ℝ):‖clippedSource W c θ x‖=‖W (c*x)‖:=by
  simp only [clippedSource,norm_mul,logPhase_norm,one_mul]

theorem clipped_bound (W:ℝ→ℂ)(B:ℝ)(hW:∀x,‖W x‖≤B)(c θ x:ℝ):
    ‖clippedSource W c θ x‖≤B:=by rw [clipped_norm];exact hW _

theorem clipped_support (W:ℝ→ℂ)(a b c cmax θ:ℝ)(ha:0<a)(hc:1≤ c)(hcm:c≤ cmax)
    (hW:Function.support W⊆Set.Icc a b):
    Function.support (clippedSource W c θ)⊆Set.Icc (a/cmax) b:=by
  intro x hx
  have hn:W (c*x)≠0:=(mul_ne_zero_iff.mp hx).2
  have hs:=hW hn
  have hcp:0<c:=zero_lt_one.trans_le hc
  have hxpos:0<x:=pos_of_mul_pos_right (ha.trans_le hs.1) hcp.le
  constructor
  · apply (div_le_iff₀ (hcp.trans_le hcm)).mpr
    exact hs.1.trans (by nlinarith)
  · have hxc:x≤ c*x:=le_mul_of_one_le_left hxpos.le hc
    exact hxc.trans hs.2

theorem clipped_support_upper (W:ℝ→ℂ)(a b c θ:ℝ)(ha:0<a)(hc:1≤ c)
    (hW:Function.support W⊆Set.Icc a b):Function.support (clippedSource W c θ)⊆Set.Iic b:=
  fun _ hx=>(clipped_support W a b c c θ ha hc le_rfl hW hx).2

end SevenEighths.InverseInitialProfileBounds

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialRetainedSum
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedSum
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns
open InverseInitialDyadicAssembly InverseSecondChildWindows Filter
local notation "O"=>ActualEisensteinCubic.O

theorem retained_sum_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(D m r T:ℝ),0≤ m→0<T→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤ c₁→c₁≤bcap→1≤ c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖∑k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ),
        windowBlock p hp hcop hg Finset.univ
          (cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)) w Ψ
          (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  have hb:0< max 1 b₀:=zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨J,Btree,Tclip,hBtree,hTclip,hwindow⟩:=
    InverseInitialRetainedWindow.retained_window_bound W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
      (fun _=>1/4) (fun _=>1) (by intros;norm_num) (by intros;norm_num)
      cap gap eps (cap+3) π hcap hgap heps (by linarith) hπ K
  obtain ⟨A,hA,hcount⟩:=retained_card_subpower (max 1 b₀) cap (4*η+τ) loss hb hcap (by positivity) hloss
  have hpowers:∀ᶠZ:ℝ in atTop,(4:ℝ)≤Z^η:=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  have hlogs:∀ᶠZ:ℝ in atTop,Tclip≤3*η*Real.log Z:=by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Tclip/(3*η)))] with Z hZ
    exact (div_le_iff₀ (by positivity : 0<3*η)).mp hZ |>.trans_eq (mul_comm _ _)
  have hevent:=window_exponent_eventual_upper (max 1 b₀) 1 hb (by norm_num)
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp (hcount.and (hpowers.and (hlogs.and hevent)))
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Zq,hC,hZq,hw⟩:=hwindow q hq
  refine ⟨A*C,max Zq Zaux,mul_pos hA hC,lt_max_of_lt_left hZq,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf D m r T hm hT
    hprodj hprod hDeq hmargin₁ hmargin₂ hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hweight
  have hZq':Zq≤Z:=(le_max_left _ _).trans hZ
  obtain ⟨hcZ,hpow,hlog,hexp⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hZp:1<Z:=hZq.trans_le hZq'
  have hDcap:D≤ cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq]
    linarith
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
  have hfc:∀x∈Sc,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
  have hlo:Z^(-η)≤(1/4:ℝ):=by
    rw [Real.rpow_neg (zero_lt_one.trans hZp).le]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) hpow
  have hnorm (k:Windows (fun _=>1) (physicalCaps (max 1 b₀) Z D T))
      (hk:k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ)):
      ‖windowBlock p hp hcop hg Finset.univ Sc w Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff) (clippedSource W₁ c₁ θ₁)
        (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*Z^(m+15*η+π+eps)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    have hsize:0< max 1 b₀*Z^D:=mul_pos hb (Real.rpow_pos_of_pos (zero_lt_one.trans hZp) D)
    have h0:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 0).val (k 0).property
    have h1:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 1).val (k 1).property
    apply hw Z hZq' Dpool hD all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
      qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod Sc hdivc hfc cutoff
      (fun i x hx=>Set.Ioo_subset_Icc_self (cutoff_support i hx))
      D (exponent Z (k 0).val) (exponent Z (k 2).val) (exponent Z (k 1).val)
      (exponent Z (k 3).val) m r η τ hη.le hηsmall hτsmall
      (fun _=>by linarith) hlo hlog hprodj hprod hDeq hmargin₁ hmargin₂ hparent
      (by linarith [h0.2,h1.1]) (Finset.mem_filter.mp hk).2 c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂
      (fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D (exponent Z (k 0).val)
        (exponent Z (k 2).val) (exponent Z (k 1).val) (exponent Z (k 3).val))) ?_
    intro x hx
    rw [norm_mul]
    have hmul {a b : ℝ} (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
      (mul_le_of_le_one_left hb₀ ha).trans hb
    apply hmul (hweight x (Finset.mem_filter.mp hx).1) (by positivity)
    unfold outerCutoff
    simp only [norm_mul]
    exact hmul (hmul (hmul (cutoff_norm_le _ _) (by positivity)
      (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hnorm).trans
  rw [Finset.sum_const, nsmul_eq_mul]
  calc
    _≤(A*Z^loss)*(C*Z^(m+15*η+π+eps)*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))):=
      mul_le_mul_of_nonneg_right (hcZ D m (4*η+τ) T hDcap hm le_rfl hT) (by positivity)
    _=_:=by rw [Real.rpow_add (zero_lt_one.trans hZp) (m+15*η+π+eps) loss];ring

end SevenEighths.InverseInitialRetainedSum

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialFiniteEnergy
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialFiniteEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

theorem finite_physical_bound_oai
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb₁:∀x,‖W₁ x‖≤B₀)(hb₂:∀x,‖W₂ x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
      (∀x∈S,x.common⊆Finset.univ)→(∀x∈S,x.overlap⊆Finset.univ)→
    ∀(D m r:ℝ),0≤ m→m≤ cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤ c₁→c₁≤bcap→1≤ c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ
        (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨J,Btree,hBtree,hretained⟩:=InverseInitialRetainedSum.retained_sum_bound
    W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨ss,Ct,hCt,htail⟩:=InverseInitialDyadicTailBound.actual_high_mass_tail (2*cap+2) 1 τ hτ
  let tailC:=Ct*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have htailC:0≤tailC:=by dsimp [tailC];positivity
  have hevent:∀ᶠZ:ℝ in atTop,max 1 b₀≤Z ∧ 64*(max 1 b₀)^2≤Z^η:=
    (eventually_ge_atTop (max 1 b₀)).and
      ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (64*(max 1 b₀)^2)))
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp hevent
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨Cr,Zr,hCr,hZr,hretained⟩:=hretained q hq
  refine ⟨Cr+tailC,max Zr Zaux,by linarith,lt_max_of_lt_left hZr,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf hcommon hoverlap
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  have hZr':Zr≤Z:=(le_max_left _ _).trans hZ
  have hZp:1<Z:=hZr.trans_le hZr'
  obtain ⟨hbZ,h64⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hDcap:D≤ cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq];linarith
  have hsize:max 1 b₀*Z^D≤Z^(2*cap+2):=by
    calc
      _≤Z*Z^D:=mul_le_mul_of_nonneg_right hbZ (Real.rpow_nonneg (by linarith) _)
      _=Z^(D+1):=by rw [Real.rpow_add (by linarith : 0<Z),Real.rpow_one];ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  have hs₁':Function.support (clippedSource W₁ c₁ θ₁)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₁ a₀ b₀ c₁ θ₁ ha₀ hc₁ hs₁ hx) (le_max_right 1 b₀)
  have hs₂':Function.support (clippedSource W₂ c₂ θ₂)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₂ a₀ b₀ c₂ θ₂ ha₀ hc₂ hs₂ hx) (le_max_right 1 b₀)
  obtain ⟨T,hT,hfreqcap⟩:=exists_source_frequency_cap p S
  have hsplit:=actual_physical_retained_tail p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ S hdiv hf w Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ
    Z D m (max 1 b₀) T (4*η+τ) hZp hs₁' hs₂' hfreqcap
  rw [hsplit]
  apply (norm_add_le _ _).trans
  have hret:=hretained Z hZr' Dpool hD all assigned hassigned hK lists Hslot coeff
    hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf
    D m r T hm hT hprodj hprod hDeq hmargin₁ hmargin₂ hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have ht:=htail p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa) Ψ hΨ
    (assignedElement assigned qelem) (all\assigned) lists coeff
    (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hac
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m η (max 1 b₀) 1 B₀ B₀
    hZp hη.le (by positivity) h64 (by linarith) hsize (by linarith) (by linarith)
    (by norm_num) hB₀ hB₀ (clipped_bound W₁ B₀ hb₁ c₁ θ₁) (clipped_bound W₂ B₀ hb₂ c₂ θ₂)
    hs₁' hs₂' Finset.univ Sc w
    (fun x hx=>hcommon x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hoverlap x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hw x (Finset.mem_filter.mp hx).1)
    (fun _=>1) (physicalCaps (max 1 b₀) Z D T) (by intros;norm_num)
    (fun x hx=>(Finset.mem_filter.mp hx).2)
  have hheight:1≤((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg θ₁]))
      (one_le_pow₀ (by linarith [norm_nonneg θ₂]))
  have hpow:Z^(-1:ℝ)≤Z^(m+15*η+π+eps+loss):=
    Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  apply (add_le_add hret ht).trans
  change Cr*Z^(m+15*η+π+eps+loss)*_+(Ct*1*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-1:ℝ))≤_
  have hh:tailC*Z^(-1:ℝ)≤tailC*Z^(m+15*η+π+eps+loss)*
      ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    calc
      _≤tailC*Z^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left hpow htailC
      _≤_:=le_mul_of_one_le_right (by positivity) hheight
  convert (preTransparency := .instances) add_le_add_left hh (Cr*Z^(m+15*η+π+eps+loss)*
    ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))) using 1 <;> dsimp [tailC] <;> ring

end SevenEighths.InverseInitialFiniteEnergy

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseInitialFiniteEnergy.finite_physical_bound_oai := @OAI.SevenEighths.InverseInitialFiniteEnergy.finite_physical_bound_oai
