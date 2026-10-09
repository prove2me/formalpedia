-- Prove2me | solution 1 for OAI.SevenEighths.InverseInitialRetainedWindow.retained_window_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:03:18.285037+00:00
-- url     : https://prove2.me/submissions/18c85f10-e654-4e43-aae7-f5c8e929e000

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Theorems.Thm_OAI_SevenEighths_InverseInitialRetainedPhysical_retained_physical_bound

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs
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
open FirstPassCubeLabels (columnLog primeProductNorm )
open ConcreteTraceCRT (eisEmbedding)

theorem mem_secondFrequencyCutoff (scale H : ℝ) (k : O)
    (hk : ‖eisEmbedding k‖^2 ≤ H/scale) : k ∈ secondFrequencyCutoff scale H := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hk
  exact_mod_cast hk.trans (Nat.le_ceil (H/scale))

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog jLabel b0Label )
open JointLogSeparation (tripleCoefficient)

end SecondPassArithmetic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Basic
namespace OAI

namespace SevenEighths.InverseMoment

theorem initial_margins_sharp {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta) :
    c₁ + delta - 9 * eta - tau ≤
      initialF r z G P delta - initialM m r z G P eta tau - Q - (z - G) ∧
    c₂ + 4 * delta - 22 * eta - 3 * tau ≤
      4 * initialF r z G P delta - 3 * initialM m r z G P eta tau -
        6 * (z - G) := by
  unfold initialF initialM
  constructor <;> linarith

theorem initial_margins {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta)
    (hc : 0 ≤ min c₁ c₂) (hdelta : 0 ≤ delta) (heta : eta ≤ min c₁ c₂ / 100)
    (htau : tau ≤ min c₁ c₂ / 100) :
    CanonicalMargins (initialF r z G P delta)
      (initialM m r z G P eta tau) Q (z - G) (3 * min c₁ c₂ / 4) := by
  obtain ⟨ha, hb⟩ := initial_margins_sharp (delta := delta) (tau := tau) h₁ h₂ hG hP hQ
  have hc₁ := min_le_left c₁ c₂
  have hc₂ := min_le_right c₁ c₂
  constructor <;> linarith

end SevenEighths.InverseMoment

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ChildCutoff
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ childFrequencyBall a R ↔ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))
  simp only [childFrequencyBall, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_,h⟩⟩
  apply mem_secondFrequencyCutoff
  apply (le_div_iff₀ hn).mpr
  simpa only [map_mul, norm_mul, mul_pow, mul_comm] using h

lemma mem_nonzeroChildFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ nonzeroChildFrequencyBall a R ↔
      0 < ‖eisEmbedding (a*k)‖^2 ∧ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding (a*k)‖^2 ↔ k ≠ 0 := by
    rw [sq_pos_iff, norm_ne_zero_iff]
    constructor
    · intro h hk; apply h; simp [hk]
    · intro hk; exact ConcreteTraceCRT.eisEmbedding_ne_zero (mul_ne_zero ha hk)
  simp only [nonzeroChildFrequencyBall, Finset.mem_erase,
    mem_childFrequencyBall a ha, hn]

end
end SevenEighths.InverseMoment

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondProfileIdentity
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem secondNormProfile_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (G₀ E₀ V₀ K₀ X₀ Y : ℝ)
    (_hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (Y*K₀/(E₀*V₀^2*X₀^2))
          ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] := by
  have hleft : (q 0/G₀)*(q 2/V₀)*(q 4/X₀) = q 0*q 2*q 4/(G₀*V₀*X₀) := by ring
  have hright : (q 0/G₀)*(q 2/V₀)*(q 5/X₀) = q 0*q 2*q 5/(G₀*V₀*X₀) := by ring
  have harg : (Y*K₀/(E₀*V₀^2*X₀^2))*(q 3/K₀)/
      ((q 1/E₀)*(q 2/V₀)^2*(q 4/X₀)*(q 5/X₀)) =
      Y*q 3/(q 1*(q 2)^2*q 4*q 5) := by
    field_simp
  have hroot : Real.sqrt (q 4/X₀)*Real.sqrt (q 5/X₀) =
      Real.sqrt (q 4)*Real.sqrt (q 5)/X₀ := by
    rw [Real.sqrt_div (hq 4).le,Real.sqrt_div (hq 5).le]
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hX.le]
  have hc0 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (0:Fin 6) = q 0/G₀ := rfl
  have hc1 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (1:Fin 6) = q 1/E₀ := rfl
  have hc2 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (2:Fin 6) = q 2/V₀ := rfl
  have hc3 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (3:Fin 6) = q 3/K₀ := rfl
  have hc4 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (4:Fin 6) = q 4/X₀ := rfl
  have hc5 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (5:Fin 6) = q 5/X₀ := rfl
  unfold secondNormProfile
  simp only [Finset.prod_const_one,one_mul,hc0,hc1,hc2,hc3,hc4,hc5]
  rw [hleft,hright,harg]
  have hrootC : (Real.sqrt (q 4/X₀):ℂ)*(Real.sqrt (q 5/X₀):ℂ) =
      (Real.sqrt (q 4):ℂ)*(Real.sqrt (q 5):ℂ)/(X₀:ℂ) := by exact_mod_cast hroot
  rw [show (↑(q 1/E₀):ℂ)*↑(q 2/V₀)*↑(Real.sqrt (q 4/X₀))*↑(Real.sqrt (q 5/X₀)) =
      (↑(q 1/E₀):ℂ)*↑(q 2/V₀)*(↑(Real.sqrt (q 4/X₀))*↑(Real.sqrt (q 5/X₀))) from by ring,
    hrootC]
  have hEc : (E₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE.ne'
  have hVc : (V₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have hXc : (X₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  push_cast
  field_simp [hEc,hVc,hXc]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondKernelMeasure
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

lemma secondRelativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (G E V K X : ℝ) (hG : 0 < G) (hE : 0 < E) (hV : 0 < V) (hK : 0 < K) (hX : 0 < X) :
    ∀ i, 0 < secondRelativeNorm q G E V K X i := by
  intro i
  fin_cases i
  · exact div_pos (hq 0) hG
  · exact div_pos (hq 1) hE
  · exact div_pos (hq 2) hV
  · exact div_pos (hq 3) hK
  · exact div_pos (hq 4) hX
  · exact div_pos (hq 5) hX

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSquarefree
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourcePrime sourceIdeal_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop in
omit [DecidableEq ι] in
theorem sourceIdeal_squarefree (S : Finset ι) : Squarefree (sourceIdeal p S) := by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (hcop hij).isRelPrime
  · intro i hi
    exact (sourcePrime p i).property.squarefree

omit [DecidableEq ι] in
lemma prime_span_coprime_of_not_mem (i : ι) (c : Eis) (hc : c ∉ Ideal.span {p i}) :
    IsCoprime (Ideal.span {p i}) (Ideal.span {c} : Ideal Eis) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hne
  have he := (inferInstance : (Ideal.span {p i}).IsMaximal).eq_of_le hne le_sup_left
  apply hc
  rw [he]
  exact (show Ideal.span {c} ≤ (Ideal.span {p i} : Ideal Eis) ⊔ Ideal.span {c} from le_sup_right)
    (Ideal.subset_span (by simp))

omit [DecidableEq ι] in
theorem sourceIdeal_coprime_of_not_mem (S : Finset ι) (c : Eis)
    (hc : ∀ i ∈ S, c ∉ Ideal.span {p i}) :
    IsCoprime (sourceIdeal p S) (Ideal.span {c} : Ideal Eis) := by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  exact IsCoprime.prod_left (fun i hi => prime_span_coprime_of_not_mem p i c (hc i hi))

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.ClippingProfiles
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
namespace SevenEighths.InverseClippingProfiles

theorem clipping_ratio_of_column_witness (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q / Z^N) ≠ 0) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  have hz : 0 < Z := by linarith
  have hn : 0 ≤ max 0 N-N := sub_nonneg.mpr (le_max_right _ _)
  refine ⟨Real.one_le_rpow hZ.le hn, ?_⟩
  by_cases hN : 0 ≤ N
  · simpa [max_eq_right hN] using hb
  · have hN' : N ≤ 0 := le_of_lt (lt_of_not_ge hN)
    rw [max_eq_left hN', zero_sub, Real.rpow_neg hz.le]
    have hsupport := (hw hwitness).2
    calc
      _ = 1 / Z^N := (one_div _).symm
      _ ≤ q / Z^N := div_le_div_of_nonneg_right hq (Real.rpow_nonneg hz.le _)
      _ ≤ b := hsupport

open InverseMoment

end SevenEighths.InverseClippingProfiles

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment

namespace SevenEighths.InverseInitialProfile

theorem original_column_scale {Z : ℝ} (hZ : 0 < Z) (D B v : ℝ) :
    Z^B * Z^v * Z^(columnCenter D B v) = Z^D := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  unfold columnCenter
  ring

theorem initial_prefactor_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ : ℝ) :
    Z^(-D) * Z^m / (Z^θ * Z^v * Z^(columnCenter D B v)) =
      Z^(prefactorCenter m D B θ) := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter prefactorCenter
  ring

theorem initial_radial_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ) :
    Z^m * Z^H / (Z^θ * (Z^v)^2 * (Z^(columnCenter D B v))^2) =
      Z^(radialCenter m H θ D B) := by
  simp only [pow_two]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter radialCenter
  ring

theorem physicalKernel_eq_secondNorm (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      ((Z^(-D)*Z^m : ℝ) : ℂ) *
        secondNormProfile (fun x => W₁ (x/Z^D)) (fun x => W₂ (x/Z^D))
          Φ (fun _ _ => 1) (Z^m) q := by
  unfold physicalKernel secondNormProfile
  rw [Real.sqrt_mul (hq 4).le]
  simp only [Finset.prod_const_one, one_mul, Complex.ofReal_div, Complex.ofReal_mul]
  ring

theorem physicalKernel_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ) : ℝ) *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1) (Z^(radialCenter m H θ D B))
          (secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))) := by
  have hn := secondNormProfile_nominal W₁ W₂ Φ
    (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v)) (Z^m)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) q hq
  rw [original_column_scale hZ D B v, initial_radial_scale hZ D B v m θ H] at hn
  rw [physicalKernel_eq_secondNorm W₁ W₂ Φ Z D m q hq, hn]
  change ((Z^(-D)*Z^m : ℝ) : ℂ) *
      (((Z^θ*Z^v*Z^(columnCenter D B v) : ℝ) : ℂ)⁻¹ * _) = _
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← div_eq_mul_inv, initial_prefactor_scale hZ D B v m θ]
  rfl

theorem relativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    {Z : ℝ} (hZ : 0 < Z) (D B v θ H : ℝ) :
    ∀ i, 0 < relativeNorm q Z D B v θ H i :=
  secondRelativeNorm_pos q hq _ _ _ _ _
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _)

end SevenEighths.InverseInitialProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem mem_freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) (U : Finset ι) :
    U ∈ freshColumns p pool w X ↔ U ⊆ pool ∧ w (primeProductNorm p U/X) ≠ 0 := by
  simp [freshColumns]

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_clipping_range (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  obtain ⟨U,hU⟩ := hn
  exact InverseClippingProfiles.clipping_ratio_of_column_witness w Z N
    (primeProductNorm p U) a b hZ (primeProductNorm_ge_one p hp U) hb hw
    ((mem_freshColumns p pool w (Z^N) U).mp hU).2

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_initial_clipping_shift (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N η : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty)
    (hthreshold : Real.log b ≤ 3*η*Real.log Z) :
    0 ≤ max 0 N-N ∧ max 0 N-N ≤ 3*η := by
  have hc := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hz _) hc.2
  rw [Real.log_rpow hz] at hl
  refine ⟨sub_nonneg.mpr (le_max_right _ _), ?_⟩
  exact (mul_le_mul_iff_left₀ (Real.log_pos hZ)).mp (hl.trans hthreshold)

end Arithmetic

end SevenEighths.InverseInitialClippedColumns

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open JointLogSeparation IdealMobiusDivisorSum InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma child_ball_neg (R : ℝ) (k : Eis) :
    -k ∈ nonzeroChildFrequencyBall 1 R ↔ k ∈ nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,map_neg,norm_neg]

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondProfileUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment
open SevenEighths.InverseInitialProfile
open SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseSecondProfileUniform

theorem positiveSource_logSchwartz (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (θ : ℝ) :
    positiveSource (CubicReflectionKernel.logSchwartz W a b ha hs hW) c θ x =
      clippedSource W c θ x := by
  simp only [positiveSource, CubicReflectionKernel.logSchwartz_apply,
    Real.exp_add, Real.exp_log hc, Real.exp_log hx, clippedSource]
  rw [mul_comm x c]

end SevenEighths.InverseSecondProfileUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseSecondChildWindows
open InverseMoment InverseSecondProfileUniform
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O

theorem positiveSource_log_bound (g : 𝓢(ℝ,ℂ)) (m bcap c θ x : ℝ)
    (_hm : 0≤ m) (hs : Function.support g⊆Set.Icc (-m) m)
    (hc : 1≤ c) (hcb : c≤bcap) (_hx : 0<x)
    (hn : positiveSource g c θ x≠0) : |Real.log x|≤ m+Real.log bcap := by
  have hc0 : 0<c := zero_lt_one.trans_le hc
  have hgn : g (Real.log x+Real.log c)≠0 := (mul_ne_zero_iff.mp hn).2
  have hh := hs hgn
  have hcl : 0≤Real.log c := Real.log_nonneg hc
  have hclb : Real.log c≤Real.log bcap := Real.log_le_log hc0 hcb
  rw [abs_le]
  constructor <;> linarith [hh.1,hh.2]

theorem positiveSource_ratio_support (g : 𝓢(ℝ,ℂ)) (m bcap c θ x : ℝ)
    (hm : 0≤ m) (hs : Function.support g⊆Set.Icc (-m) m)
    (hc : 1≤ c) (hcb : c≤bcap) (hx : 0<x)
    (hn : positiveSource g c θ x≠0) :
    x∈Set.Icc (Real.exp (-(m+Real.log bcap))) (Real.exp (m+Real.log bcap)) := by
  have hh := (abs_le.mp (positiveSource_log_bound g m bcap c θ x hm hs hc hcb hx hn))
  exact ⟨(Real.le_log_iff_exp_le hx).mp hh.1,(Real.log_le_iff_le_exp hx).mp hh.2⟩

theorem translated_log_bound (a b x ρ B : ℝ) (ha : 0<a)
    (hx : x∈Set.Icc a b) (hρ : |ρ|≤B) :
    |Real.log x+ρ|≤|Real.log a|+|Real.log b|+B := by
  have hx0 := ha.trans_le hx.1
  have hlo := Real.log_le_log ha hx.1
  have hhi := Real.log_le_log hx0 hx.2
  have hl : |Real.log x|≤|Real.log a|+|Real.log b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
    · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]
  exact (abs_add_le _ _).trans (add_le_add hl hρ)

theorem fixed_windows (m bcap : ℝ) (lo hi : Fin 4→ℝ) (Bρ : Fin 6→ℝ)
    (hm : 0≤ m) (_hcap : 1≤bcap) (hlo : ∀ i,0<lo i)
    (hhi : ∀ i,lo i≤hi i) (hBρ : ∀ i,0≤Bρ i) :
    ∃ (w : 𝓢(ℝ,ℂ)) (U : Fin 6→𝓢(ℝ,ℂ)) (M : Fin 6→ℝ) (a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀ i,0≤M i) ∧ (∀ i,HasCompactSupport (U i : ℝ→ℂ)) ∧
      (∀ i,Function.support (U i)⊆Set.Icc (-M i) (M i)) ∧
      (∀ (g : 𝓢(ℝ,ℂ)),Function.support g⊆Set.Icc (-m) m →
        ∀ (c θ u v n : ℝ),1≤ c → c≤bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 2) (hi 2) → 0<n →
        positiveSource g c θ (u*v*n)≠0 → w n=1) ∧
      (∀ (q : Fin 6→ℝ) (ρ : Fin 6→ℝ),
        (∀ i,|ρ i|≤Bρ i) →
        (∀ i : Fin 4,q (outerIndex i)∈Set.Icc (lo i) (hi i)) →
        w (q 4)≠0 → w (q 5)≠0 → ∀ i,U i (Real.log (q i)+ρ i)=1) := by
  let R := m+Real.log bcap
  let a := Real.exp (-R)/(hi 0*hi 2)
  let b := Real.exp R/(lo 0*lo 2)
  have hhi0 (i : Fin 4) : 0<hi i := (hlo i).trans_le (hhi i)
  have ha : 0<a := div_pos (Real.exp_pos _) (mul_pos (hhi0 0) (hhi0 2))
  have hb : 0<b := div_pos (Real.exp_pos _) (mul_pos (hlo 0) (hlo 2))
  obtain ⟨w,hwc,hwone,hws⟩ := positive_cutoff a (a+b+1) ha (by linarith)
  let l : Fin 6→ℝ := ![lo 0,lo 1,lo 2,lo 3,a/2,a/2]
  let u : Fin 6→ℝ := ![hi 0,hi 1,hi 2,hi 3,(a+b+1)+1,(a+b+1)+1]
  have hl (i : Fin 6) : 0<l i := by
    fin_cases i
    · exact hlo 0
    · exact hlo 1
    · exact hlo 2
    · exact hlo 3
    · exact half_pos ha
    · exact half_pos ha
  let H (i : Fin 6) := |Real.log (l i)|+|Real.log (u i)|+Bρ i
  have hH (i : Fin 6) : 0≤H i := add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hBρ i)
  choose V hVc hVs hVone hVsupport hVzero using
    fun i : Fin 6 => FourierBridge.exists_complex_smooth_cutoff (H i) (hH i)
  let U (i : Fin 6) : 𝓢(ℝ,ℂ) := (hVc i).toSchwartzMap (hVs i)
  refine ⟨w,U,(fun i=>H i+1),a/2,(a+b+1)+1,half_pos ha,by linarith,hwc,hws,
    (fun i=>by linarith [hH i]),hVc,(fun i=>(subset_tsupport _).trans (hVsupport i)),?_,?_⟩
  · intro g hg c θ u v n hc hcb hu hv hn hnz
    have hu0 := (hlo 0).trans_le hu.1
    have hv0 := (hlo 2).trans_le hv.1
    have hs := positiveSource_ratio_support g m bcap c θ (u*v*n) hm hg hc hcb
      (mul_pos (mul_pos hu0 hv0) hn) hnz
    have hnlo : a≤n := by
      apply (div_le_iff₀ (mul_pos (hhi0 0) (hhi0 2))).mpr
      calc
        _ ≤ u*v*n := hs.1
        _ ≤ (hi 0*hi 2)*n := mul_le_mul_of_nonneg_right
          (mul_le_mul hu.2 hv.2 hv0.le (hhi0 0).le) hn.le
        _ = _ := by ring
    have hnhi : n≤b := by
      apply (le_div_iff₀ (mul_pos (hlo 0) (hlo 2))).mpr
      calc
        _ = (lo 0*lo 2)*n := by ring
        _ ≤ u*v*n := mul_le_mul_of_nonneg_right
          (mul_le_mul hu.1 hv.1 (hlo 2).le hu0.le) hn.le
        _ ≤ _ := hs.2
    exact hwone n ⟨hnlo,by linarith⟩
  · intro q ρ hρ hblock hleft hright i
    have hq (k : Fin 6) : q k∈Set.Icc (l k) (u k) := by
      fin_cases k
      · exact hblock 0
      · exact hblock 1
      · exact hblock 2
      · exact hblock 3
      · exact hws (subset_tsupport _ hleft)
      · exact hws (subset_tsupport _ hright)
    exact hVone i _ (translated_log_bound (l i) (u i) (q i) (ρ i) (Bρ i) (hl i) (hq i) (hρ i))

end SevenEighths.InverseSecondChildWindows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialQuotientGeometry
namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalQuadraticSieve
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialQuotientGeometry

local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)

variable (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_nonzero {J : ℕ} (S : Finset (Source (ι:=ι) J)) :
    ∀ t ∈ quotientSet p S, t ≠ 0 := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  exact sourceIdeal_ne_zero p hp _

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotient_norm_eq {J : ℕ} (x : Source (ι:=ι) J) (hdiv : x.divisor ⊆ x.common) :
    (Ideal.absNorm (sourceIdeal p (x.common\x.divisor)) : ℝ) =
      (Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Ideal.absNorm (sourceIdeal p x.divisor) := by
  have he : sourceIdeal p x.divisor * sourceIdeal p (x.common\x.divisor) = sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common\x.divisor) Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hdiv]
  have hn := congrArg (fun I : Ideal Eis => (Ideal.absNorm I : ℝ)) he
  simp only [map_mul,Nat.cast_mul] at hn
  have hd : (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)
  apply (eq_div_iff hd).mpr
  simpa only [mul_comm] using hn

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem retained_norm_windows {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    {x : Source (ι:=ι) J} (hx : x ∈ retained p S A ψC ψd Z B θ) :
    (Ideal.absNorm (sourceIdeal p x.common) : ℝ) ≤ bC*Z^B ∧
      ad*Z^θ ≤ (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) := by
  have hn := (Finset.mem_filter.mp hx).2
  have hnC : ψC ((Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Z^B) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
  have hnd : ψd ((Ideal.absNorm (sourceIdeal p x.divisor) : ℝ)/Z^θ) ≠ 0 :=
    (mul_ne_zero_iff.mp hn).2
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hC hnC).2,
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hd hnd).1⟩

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_quotient_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) :
    ∀ t ∈ quotientSet p (retained p S A ψC ψd Z B θ),
      (Ideal.absNorm t : ℝ) ≤ Z^(B-θ+2*η) := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  have hw := retained_norm_windows p S A ψC ψd aC bC ad bd Z B θ hZ hC hd hx
  rw [quotient_norm_eq p hp x (hdiv x (Finset.mem_filter.mp hx).1)]
  have hc : (Ideal.absNorm (sourceIdeal p x.common) : ℝ) ≤ Z^(B+η) := by
    apply (hw.1.trans (mul_le_mul_of_nonneg_right hCup (Real.rpow_pos_of_pos hZ _).le)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  have he : Z^(θ-η) ≤ (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) := by
    apply le_trans _ hw.2
    calc
      _ = Z^(-η)*Z^θ := by rw [←Real.rpow_add hZ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdlo (Real.rpow_pos_of_pos hZ _).le
  calc
    _ ≤ Z^(B+η)/Z^(θ-η) := div_le_div₀ (by positivity) hc (Real.rpow_pos_of_pos hZ _) he
    _ = _ := by rw [←Real.rpow_sub hZ]; congr 1; ring

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem nonempty_radius {J : ℕ} (S : Finset (Source (ι:=ι) J)) (Z P η : ℝ)
    (hZ : 1 < Z) (hne : (quotientSet p S).Nonempty)
    (hnorm : ∀ t ∈ quotientSet p S, (Ideal.absNorm t : ℝ) ≤ Z^(P+2*η)) :
    1 ≤ Z^(P+2*η) ∧ 0 ≤ P+2*η := by
  obtain ⟨t,ht⟩ := hne
  have ht0 := quotientSet_nonzero p hp S t ht
  have hn : (1:ℝ) ≤ Ideal.absNorm t := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ht0)
  have hh := hn.trans (hnorm t ht)
  refine ⟨hh,?_⟩
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero] using hh)

theorem assigned_register {σ : Type*} [DecidableEq σ]
    (all assigned : Finset σ) (ha : assigned ⊆ all) (z : σ → ℝ)
    (hz : ∀ i ∈ all, 0 ≤ z i) :
    0 ≤ assignedCenter assigned z ∧ 0 ≤ assignedCenter (all\assigned) z ∧
      assignedCenter all z - assignedCenter assigned z = assignedCenter (all\assigned) z := by
  refine ⟨Finset.sum_nonneg (fun i hi => hz i (ha hi)),
    Finset.sum_nonneg (fun i hi => hz i (Finset.mem_sdiff.mp hi).1),?_⟩
  unfold assignedCenter
  have h := Finset.sum_sdiff ha (f := z)
  linarith

theorem assigned_norm_bound {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ) (Z : ℝ) (hZ : 0 < Z)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0) :
    (Ideal.absNorm (Ideal.span {assignedElement slots q}) : ℝ) ≤
      (∏ i ∈ slots, b i)*Z^(assignedCenter slots z) := by
  have hb : ∀ i ∈ slots, (Ideal.absNorm (Ideal.span {q i}) : ℝ) ≤ b i*Z^(z i) := by
    intro i hi
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hW i hi (hret i hi)).2
  have hp := Finset.prod_le_prod (fun i _ => (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {q i})))) hb
  simpa only [assignedElement,FiniteGaussPhase.span_finset_prod,map_prod,Nat.cast_prod,
    Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,assignedCenter] using hp

theorem assigned_norm_power {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ) (Z η : ℝ) (hZ : 0 < Z)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η) :
    (Ideal.absNorm (Ideal.span {assignedElement slots q}) : ℝ) ≤
      Z^(assignedCenter slots z+η) := by
  apply (assigned_norm_bound slots q z a b W Z hZ hW hret).trans
  calc
    _ ≤ Z^η*Z^(assignedCenter slots z) := mul_le_mul_of_nonneg_right hthreshold (by positivity)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem span_source_puncture {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (hpr : ∀ i, λ₀^2 ∣ p i-1) (j : Eis)
    {t : Ideal Eis} (ht : t ∈ quotientSet p S) :
    Ideal.span {j*primaryGenerator t} = t*Ideal.span {j} := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  rw [sourceIdeal_gen p hp hpr]
  simp only [sourceIdeal,Ideal.span_singleton_mul_span_singleton,mul_comm]

end SevenEighths.InverseInitialQuotientGeometry

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

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem relative_column_left (x : Point ι) (Z D B v θ H : ℝ) :
    relativeNorm (coordinates p x) Z D B v θ H 4=columnRatio p x.left Z D B v := rfl

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem relative_column_right (x : Point ι) (Z D B v θ H : ℝ) :
    relativeNorm (coordinates p x) Z D B v θ H 5=columnRatio p x.right Z D B v := rfl

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem columnRatio_actual (N : Finset ι) (Z D B v : ℝ) :
    columnRatio p N Z D B v=primeProductNorm p N/Z^(columnCenter D B v) := by
  unfold columnRatio sourceIdeal primeProductNorm
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerGeometry
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerGeometry
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialProfile InverseInitialClippedColumns ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem outerCoefficient_nonzero_coprime
    (Ψ:Eis→*ℂ)(j:Eis)(x:Point ι)(ρ:SecondRayIndex)
    (hn:outerCoefficient p hp hcop hg Ψ j x ρ≠0) :
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common) := by
  apply sourceIdeal_coprime_of_not_mem p
  intro i hi hc
  have hmc : j*(∏k∈x.common,p k)∈Ideal.span {p i} := Ideal.mul_mem_left _ j hc
  have hz : rowCoprimeMask (fun i=>Ideal.span {p i}) x.overlap (j*(∏k∈x.common,p k))=0 := by
    simp only [rowCoprimeMask,if_pos (show ∃i∈x.overlap,j*(∏k∈x.common,p k)∈Ideal.span {p i}
      from ⟨i,hi,hmc⟩)]
  apply hn
  simp only [outerCoefficient,initialColumn,hz,mul_zero,zero_mul,star_zero]

omit [DecidableEq ι] in
theorem initial_child_label_norm (x:Source (ι:=ι) 0)(u:Eisˣ) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)=
      (sourceIdeal p x.divisor).absNorm*(sourceIdeal p x.overlap).absNorm := by
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)=_
  simp only [map_mul,Nat.cast_mul]

include hp in

theorem initial_child_row_norm (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ) :
    ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2=
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2 := by
  change ‖eisEmbedding (primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency))‖^2=_
  have he : primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency)=
      ((u^5:Eisˣ):Eis)*(primaryGenerator (sourceIdeal p x.divisor)*x.frequency) := by
    change primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency)=
      (u:Eis)^5*(primaryGenerator (sourceIdeal p x.divisor)*x.frequency)
    ring
  rw [he,GaussGeneratorTransport.norm_eisEmbedding_unit_mul,map_mul,norm_mul,mul_pow]
  rw [eisEmbedding_norm_sq_eq_absNorm_span,sourceIdeal_gen p hp hpr]
  rfl

include hp in
theorem initial_child_row_ball (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ)(R:ℝ) :
    (initialChild (toTuple p (sectorSource u x))).2.2∈nonzeroChildFrequencyBall 1 R ↔
    0<((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2 ∧
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2≤R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,initial_child_row_norm p hp hpr]

include hp in

theorem initial_child_enclosures
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:‖eisEmbedding x.frequency‖^2≤Z^(H+η)) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)≤Z^(θ+v+2*η) ∧
      ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2≤Z^(θ+H+2*η) := by
  rw [initial_child_label_norm p,initial_child_row_norm p hp hpr]
  constructor
  · apply (mul_le_mul hd hv (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  · apply (mul_le_mul hd hh (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring

end SevenEighths.InverseInitialEnergyCallerGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSourceMask
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerSourceMask
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialProfile ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_coprimeSource
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(H:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j H W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (coprimeSource p S)) (w∘erasePoint)
      Ψ j H W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,coprimeSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hc:IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common)
  · rw [if_pos hc]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    have hxpoint : sourcePoint x N M∈pointSource pool S := by
      apply Finset.mem_biUnion.mpr
      refine ⟨x,hx,?_⟩
      apply Finset.mem_image.mpr
      exact ⟨(N,M),Finset.mem_product.mpr ⟨hN,hM⟩,rfl⟩
    have hv := pointSource_valid pool S hdiv hf _ hxpoint
    rw [physicalTerm_extracted p hp hcop hg hpr Ψ j H W₁ W₂ Φ Z D m _ hv ρ]
    have hz : outerCoefficient p hp hcop hg Ψ j (sourcePoint x N M) ρ=0 := by
      by_contra hn
      exact hc (outerCoefficient_nonzero_coprime p hp hcop hg Ψ j (sourcePoint x N M) ρ hn)
    simp only [hz,zero_mul,mul_zero]

include hcop in
theorem retained_child_squarefree
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    Squarefree (initialChild (toTuple p (sectorSource u x))).2.1 := by
  obtain ⟨hxs,hcoprime⟩ := Finset.mem_filter.mp hx
  change Squarefree (sourceIdeal p x.divisor*sourceIdeal p x.overlap)
  have hc := hcoprime.symm.of_isCoprime_of_dvd_left (sourceIdeal_dvd p _ _ (hdiv x hxs))
  exact squarefree_mul_iff.mpr ⟨hc.isRelPrime,sourceIdeal_squarefree p hcop _,
    sourceIdeal_squarefree p hcop _⟩

omit [DecidableEq ι] in
theorem child_label_mem (S:Finset (Source (ι:=ι) 0))
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    (initialChild (toTuple p (sectorSource u x))).2.1∈childLabels p S :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

end SevenEighths.InverseInitialEnergyCallerSourceMask

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerRanges
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerRanges
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask
open InverseInitialProfile ConcreteTraceCRT CanonicalQuadraticSieve
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp hcop hg

omit [DecidableEq ι] in
theorem sourceIdeal_admissible (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset ι) : Admissible (sourceIdeal p S) := by
  refine ⟨sourceIdeal_ne_zero p hp S,sourceIdeal_squarefree p hcop S,?_⟩
  intro P hP
  obtain ⟨hprime,hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff
    (sourceIdeal_ne_zero p hp S)).mp hP
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod] at hdiv
  obtain ⟨i,hi,hPi⟩ := (hprime.dvd_finsetProd_iff (fun i=>Ideal.span {p i})).mp hdiv
  have he := (prime_dvd_prime_iff_eq hprime (sourcePrime p i).property).mp hPi
  rw [he]
  exact ⟨hg i,hc i⟩

theorem retained_label_admissible (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    Admissible (initialChild (toTuple p (sectorSource u x))).2.1 := by
  have hs := (supported_mul_iff (sourceIdeal p x.divisor) (sourceIdeal p x.overlap)).mpr
    ⟨admissible_supported (sourceIdeal_admissible p hp hcop hg hc _),
      admissible_supported (sourceIdeal_admissible p hp hcop hg hc _)⟩
  exact ⟨hs.1,retained_child_squarefree p hcop S hdiv hx u,hs.2⟩

theorem childLabels_subset_range
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (Z θ v η:ℝ)(hZ:0<Z)
    (hd:∀x∈coprimeSource p S,((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:∀x∈coprimeSource p S,((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η)) :
    childLabels p S⊆idealRange (Z^(θ+v+2*η)) := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  apply mem_idealRange.mpr
  refine ⟨retained_label_admissible p hp hcop hg hc S hdiv hx 1,?_⟩
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)≤_
  rw [map_mul,Nat.cast_mul]
  apply (mul_le_mul (hd x hx) (hv x hx) (by positivity) (by positivity)).trans_eq
  rw [←Real.rpow_add hZ]
  congr 1
  ring

theorem canonical_child_domains
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (hf:∀x∈S,x.frequency≠0)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:∀x∈coprimeSource p S,((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:∀x∈coprimeSource p S,((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:∀x∈coprimeSource p S,‖eisEmbedding x.frequency‖^2≤Z^(H+η)) :
    ∀x∈coprimeSource p S,∀u:Eisˣ,
      (initialChild (toTuple p (sectorSource u x))).2.1∈idealRange (Z^(θ+v+2*η)) ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈
        nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)) := by
  intro x hx u
  refine ⟨childLabels_subset_range p hp hcop hg hc hpr S hdiv Z θ v η hZ hd hv
    (child_label_mem p S hx u),?_⟩
  rw [initial_child_row_ball p hp hpr]
  refine ⟨mul_pos ?_ (sq_pos_of_pos (norm_pos_iff.mpr
    (eisEmbedding_ne_zero (hf x (Finset.mem_filter.mp hx).1)))),?_⟩
  · exact_mod_cast Nat.pos_of_ne_zero (fun h=>sourceIdeal_ne_zero p hp x.divisor
      (Ideal.absNorm_eq_zero_iff.mp h))
  · have he := (initial_child_enclosures p hp hpr x u Z θ v H η hZ
      (hd x hx) (hv x hx) (hh x hx)).2
    rwa [initial_child_row_norm p hp hpr] at he

end SevenEighths.InverseInitialEnergyCallerRanges

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
open InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem sourceRelative_four (x:Source (ι:=ι) 0)(N M:Finset ι)
    (Z D B v θ H:ℝ)(i:Fin 4) :
    relativeNorm (coordinates p (sourcePoint x N M)) Z D B v θ H (InverseSecondChildWindows.outerIndex i)=
      sourceRelative p x Z D B v θ H (InverseSecondChildWindows.outerIndex i) := by
  fin_cases i <;> simp only [InverseSecondChildWindows.outerIndex,sourceRelative,relativeNorm,
    coordinates,sourcePoint,physicalCoordinates,secondRelativeNorm,Fin.castLE,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Matrix.cons_val_zero',Matrix.cons_val_succ']

theorem windowSource_four_nonzero
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ)
    {x:Point ι}(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H))(i:Fin 4) :
    ψ i (relativeNorm (coordinates p x) Z D B v θ H (InverseSecondChildWindows.outerIndex i))≠0 := by
  obtain ⟨s,hs,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  have ho := (Finset.mem_filter.mp hs).2
  change outerCutoff ψ (sourceRelative p s Z D B v θ H)≠0 at ho
  rw [sourceRelative_four]
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  fin_cases i
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseInitialEnergyCallerWindows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindowGeometry
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerWindowGeometry
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerGeometry
open InverseInitialProfile InverseInitialKernelBridge ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

theorem retained_source_windows
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H:ℝ)(hZ:0<Z){x:Source (ι:=ι) 0}
    (hx:x∈windowSource p S ψ Z D B v θ H) :
    ((sourceIdeal p x.common).absNorm:ℝ)≤hi 0*Z^B ∧
    lo 1*Z^θ≤((sourceIdeal p x.divisor).absNorm:ℝ) ∧
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤hi 1*Z^θ ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤hi 2*Z^v ∧
    ‖eisEmbedding x.frequency‖^2≤hi 3*Z^H := by
  have hm : sourcePoint x ∅ ∅∈pointSource ∅ (windowSource p S ψ Z D B v θ H) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(∅,∅),by simp,rfl⟩
  have hh (i:Fin 4) := hψ i (windowSource_four_nonzero p ∅ S ψ Z D B v θ H hm i)
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  change ((sourceIdeal p x.common).absNorm:ℝ)/Z^B∈Set.Icc (lo 0) (hi 0) at h0
  change ((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ∈Set.Icc (lo 1) (hi 1) at h1
  change ((sourceIdeal p x.overlap).absNorm:ℝ)/Z^v∈Set.Icc (lo 2) (hi 2) at h2
  change ‖eisEmbedding x.frequency‖^2/Z^H∈Set.Icc (lo 3) (hi 3) at h3
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h0.2,
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h1.1,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h1.2,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h2.2,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h3.2⟩

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
include hp

end SevenEighths.InverseInitialEnergyCallerWindowGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalDomains
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalDomains
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerWindowGeometry
open InverseInitialEnergyCallerSourceMask InverseInitialEnergyCallerRanges
open InverseInitialEnergyCallerSource CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem window_power_bounds
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:0<Z)(hhi:∀i,hi i≤Z^η)
    {x:Source (ι:=ι) 0}(hx:x∈windowSource p S ψ Z D B v θ H):
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η) ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η) ∧
    ‖eisEmbedding x.frequency‖^2≤Z^(H+η) := by
  obtain ⟨_,_,hd,hv,hh⟩:=retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  have hpow (i:Fin 4)(r:ℝ):hi i*Z^r≤Z^(r+η):=by
    rw [Real.rpow_add hZ]
    exact (mul_le_mul_of_nonneg_right (hhi i) (Real.rpow_nonneg hZ.le _)).trans_eq (mul_comm _ _)
  exact ⟨hd.trans (hpow 1 θ),hv.trans (hpow 2 v),hh.trans (hpow 3 H)⟩

include hp hcop hg in
theorem actual_window_domains
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:0<Z)(hhi:∀i,hi i≤Z^η):
    ∀x∈coprimeSource p (windowSource p S ψ Z D B v θ H),∀u:Oˣ,
      (initialChild (toTuple p (sectorSource u x))).2.1∈idealRange (Z^(θ+v+2*η)) ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈
        nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)) := by
  apply canonical_child_domains p hp hcop hg hc hpr (windowSource p S ψ Z D B v θ H)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1) Z θ v H η hZ
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).1
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).2.1
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).2.2

end SevenEighths.InverseInitialCanonicalDomains

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerState
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerState
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialQuotientGeometry
local notation "Eis"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem windowSource_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    windowSource p S ψ Z D B v θ H ⊆ retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,?_⟩
  have hn := (Finset.mem_filter.mp hx).2
  have hh := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  change ψ 0 (((sourceIdeal p x.common).absNorm:ℝ)/Z^B)*
    ψ 1 (((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ)≠0 at hh
  simpa only [sourceWeight,one_mul] using hh

theorem window_quotient_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    quotientSet p (windowSource p S ψ Z D B v θ H) ⊆
      quotientSet p (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ) :=
  Finset.image_subset_image (windowSource_subset_retained p S ψ Z D B v θ H)

variable (hp:∀i,p i≠0)
include hp

end SevenEighths.InverseInitialEnergyCallerState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalState
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerWindowGeometry InverseInitialEnergyCallerGeometry
open InverseInitialEnergyCallerRanges CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

theorem full_puncture_width_exact (Z:ℝ)(hZ:1<Z)(t:Ideal O)(j:O)
    (hm:j*primaryGenerator t≠0):
    0≤fullPunctureWidth Z t j ∧
      ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) := by
  have hn:(1:ℝ)≤Ideal.absNorm (Ideal.span {j*primaryGenerator t}) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hm))
  constructor
  · unfold fullPunctureWidth Real.logb
    exact div_nonneg (Real.log_nonneg hn) (Real.log_pos hZ).le
  · rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (zero_lt_one.trans_le hn)).symm

theorem full_product_width_bound (Z P G η:ℝ)(hZ:1<Z)(t:Ideal O)(j:O)
    (hm:j*primaryGenerator t≠0)
    (hspan:Ideal.span {j*primaryGenerator t}=t*Ideal.span {j})
    (ht:(t.absNorm:ℝ)≤Z^(P+2*η))
    (hj:(Ideal.absNorm (Ideal.span {j}):ℝ)≤Z^(G+η)):
    fullPunctureWidth Z t j≤P+G+3*η := by
  have hz:=zero_lt_one.trans hZ
  have hpos:0<(Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hm))
  have hb:(Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ)≤Z^(P+G+3*η):=by
    rw [hspan,map_mul,Nat.cast_mul]
    apply (mul_le_mul ht hj (by positivity) (Real.rpow_nonneg hz.le _)).trans_eq
    rw [←Real.rpow_add hz]
    congr 1
    ring
  unfold fullPunctureWidth Real.logb
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  simpa only [Real.log_rpow hz] using Real.log_le_log hpos hb

theorem physical_row_width_le (m r z G B θ H η τ:ℝ)
    (hcut:radialCenter m H θ (r+z-2*G) B≤4*η+τ):
    θ+H+2*η≤ initialM m r z G (B-θ) η τ := by
  unfold radialCenter at hcut
  unfold initialM
  linarith

theorem enlarged_initial_margins (m r z G B θ v H η τ Q c₁ c₂:ℝ)
    (h₁:r+2*z≤ m-c₁)(h₂:2*r+8*z≤3*m-c₂)
    (hG:0≤G)(hP:-2*η≤B-θ)(hQ:Q≤B-θ+G+3*η)
    (hc:0≤ min c₁ c₂)(hη:0≤η)(hηsmall:η≤ min c₁ c₂/100)
    (hτ:τ≤ min c₁ c₂/100)
    (hcut:radialCenter m H θ (r+z-2*G) B≤4*η+τ):
    CanonicalMargins
      (max 0 (r+z-2*G-B-v)+(θ+v+2*η)) (θ+H+2*η) Q (z-G)
      (3*min c₁ c₂/4) := by
  have hd:0≤ max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v):=
    sub_nonneg.mpr (le_max_right _ _)
  have hh:=initial_margins (delta:=max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v))
    h₁ h₂ hG hP hQ hc hd hηsmall hτ
  have hr:=physical_row_width_le m r z G B θ H η τ hcut
  unfold CanonicalMargins at hh ⊢
  unfold initialF at hh
  constructor <;> linarith [hh.1,hh.2]

end SevenEighths.InverseInitialCanonicalState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalStateSource
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerWindowGeometry InverseInitialEnergyCallerGeometry
open InverseInitialEnergyCallerRanges CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem live_widths_nonnegative
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1<Z)(hhi:∀i,hi i≤Z^η)
    {x:Source (ι:=ι) 0}(hx:x∈windowSource p S ψ Z D B v θ H)
    (hf:x.frequency≠0):
    0≤θ+v+2*η ∧ 0≤θ+H+2*η := by
  have hz:=zero_lt_one.trans hZ
  obtain ⟨_,_,hd,hv,hh⟩:=retained_source_windows p S ψ lo hi hψ Z D B v θ H hz hx
  have bound (a c:ℝ)(i:Fin 4)(ha:a≤hi i*Z^c):a≤Z^(c+η):=by
    apply (ha.trans (mul_le_mul_of_nonneg_right (hhi i) (Real.rpow_nonneg hz.le c))).trans_eq
    rw [←Real.rpow_add hz]
    congr 1
    ring
  obtain ⟨hlabel,hrow⟩:=initial_child_enclosures p hp hpr x 1 Z θ v H η hz
    (bound _ _ 1 hd) (bound _ _ 2 hv) (bound _ _ 3 hh)
  have hI:(1:ℝ)≤Ideal.absNorm (initialChild (toTuple p (sectorSource 1 x))).2.1:=by
    have hne:(initialChild (toTuple p (sectorSource 1 x))).2.1≠0:=
      mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hne)
  have hdiv:(1:ℝ)≤(sourceIdeal p x.divisor).absNorm:=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _))
  have hfreq:(1:ℝ)≤‖eisEmbedding x.frequency‖^2:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hf))
  have hr:(1:ℝ)≤‖eisEmbedding (initialChild (toTuple p (sectorSource 1 x))).2.2‖^2:=by
    rw [initial_child_row_norm p hp hpr]
    exact one_le_mul_of_one_le_of_one_le hdiv hfreq
  constructor
  · exact (Real.rpow_le_rpow_left_iff hZ).mp
      (by simpa only [Real.rpow_zero] using hI.trans hlabel)
  · exact (Real.rpow_le_rpow_left_iff hZ).mp
      (by simpa only [Real.rpow_zero] using hr.trans hrow)

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem retained_full_puncture
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(D v H aC bC ad bd Z B θ η G:ℝ)(hZ:1<Z)
    (hC:Function.support (ψ 0)⊆Set.Icc aC bC)
    (hd:Function.support (ψ 1)⊆Set.Icc ad bd)
    (hCup:bC≤Z^η)(hdlo:Z^(-η)≤ad)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (j:O)(hj:j≠0)(hnj:(Ideal.absNorm (Ideal.span {j}):ℝ)≤Z^(G+η))
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H)):
    j*primaryGenerator t≠0 ∧ 0≤fullPunctureWidth Z t j ∧
    ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    fullPunctureWidth Z t j≤B-θ+G+3*η := by
  have hspan:=span_source_puncture p hp (windowSource p S ψ Z D B v θ H) hpr j ht
  have ht0:=quotientSet_nonzero p hp (windowSource p S ψ Z D B v θ H) t ht
  have hm:j*primaryGenerator t≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [hspan]
    exact mul_ne_zero ht0 (Ideal.span_singleton_eq_bot.not.mpr hj)
  have hret:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hnt:=retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
    aC bC ad bd Z B θ η (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv t hret
  obtain ⟨hn,he⟩:=full_puncture_width_exact Z hZ t j hm
  exact ⟨hm,hn,he,full_product_width_bound Z (B-θ) G η hZ t j hm hspan hnt hnj⟩

end SevenEighths.InverseInitialCanonicalState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalStateWindow
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_window_state
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1<Z)(hη:0≤η)
    (hhi:∀i,hi i≤Z^η)(hdlo:Z^(-η)≤lo 1)
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    {σ:Type*}[DecidableEq σ](all assigned:Finset σ)(hassigned:assigned⊆all)
    (q:σ→O)(z a b:σ→ℝ)(W:σ→ℝ→ℂ)
    (hz:∀i∈all,0≤z i)(hq:∀i∈assigned,q i≠0)
    (hW:∀i∈assigned,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hret:∀i∈assigned,W i ((Ideal.absNorm (Ideal.span {q i}):ℝ)/Z^(z i))≠0)
    (hthreshold:(∏i∈assigned,b i)≤Z^η)
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r τ c₁ c₂:ℝ)(hD:D=r+assignedCenter all z-2*assignedCenter assigned z)
    (h₁:r+2*assignedCenter all z≤ m-c₁)
    (h₂:2*r+8*assignedCenter all z≤3*m-c₂)
    (hc:0≤ min c₁ c₂)(hηsmall:η≤ min c₁ c₂/100)(hτ:τ≤ min c₁ c₂/100)
    (hcut:radialCenter m H θ D B≤4*η+τ)
    (hclip:max 0 (D-B-v)-(D-B-v)≤3*η):
    let N:=max 0 (D-B-v)
    let V:=θ+v+2*η
    let M:=θ+H+2*η
    let j:=assignedElement assigned q
    j*primaryGenerator t≠0 ∧ 0≤N ∧ 0≤V ∧ 0≤M ∧
    0≤fullPunctureWidth Z t j ∧
    ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    CanonicalMargins (N+V) M (fullPunctureWidth Z t j)
      (assignedCenter (all\assigned) z+η) (min c₁ c₂/2) ∧
    N+V≤ r+assignedCenter all z+7*η ∧
    M≤ r+assignedCenter all z+7*η ∧
    N+V-(N+(θ+v))=2*η := by
  dsimp only
  have hretained:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hP: -2*η≤B-θ:=by
    have hn:=(nonempty_radius p hp (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ)
      Z (B-θ) η hZ ⟨t,hretained⟩
      (retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
        (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZ)
        (hψ 0) (hψ 1) (hhi 0) hdlo hdiv)).2
    linarith
  have hreg:=assigned_register all assigned hassigned z hz
  have hj:assignedElement assigned q≠0:=Finset.prod_ne_zero_iff.mpr hq
  have hnj:=assigned_norm_power assigned q z a b W Z η (zero_lt_one.trans hZ) hW hret hthreshold
  obtain ⟨hm,hQ0,hnorm,hQ⟩:=retained_full_puncture p hp hpr S ψ D v H
    (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (assignedCenter assigned z) hZ
    (hψ 0) (hψ 1) (hhi 0) hdlo hdiv (assignedElement assigned q) hj hnj ht
  obtain ⟨x,hx,hxt⟩:=Finset.mem_image.mp ht
  obtain ⟨hV,hM⟩:=live_widths_nonnegative p hp hpr S ψ lo hi hψ Z D B v θ H η hZ hhi
    hx (hf x (Finset.mem_filter.mp hx).1)
  have hmg:=enlarged_initial_margins m r (assignedCenter all z) (assignedCenter assigned z)
    B θ v H η τ (fullPunctureWidth Z t (assignedElement assigned q)) c₁ c₂
    h₁ h₂ hreg.1 hP hQ hc hη hηsmall hτ (by simpa only [hD] using hcut)
  rw [←hD,hreg.2.2] at hmg
  have hactual:CanonicalMargins (max 0 (D-B-v)+(θ+v+2*η)) (θ+H+2*η)
      (fullPunctureWidth Z t (assignedElement assigned q))
      (assignedCenter (all\assigned) z+η) (min c₁ c₂/2):=by
    unfold CanonicalMargins at hmg ⊢
    constructor <;> linarith [hmg.1,hmg.2]
  have hF:max 0 (D-B-v)+(θ+v+2*η)≤ r+assignedCenter all z+7*η:=by
    rw [hD] at hclip ⊢
    linarith [hreg.1]
  have hMF:θ+H+2*η≤ max 0 (D-B-v)+(θ+v+2*η):=by
    have hh:=hactual.1
    linarith [hreg.2.1]
  exact ⟨hm,le_max_left _ _,hV,hM,hQ0,hnorm,hactual,hF,hMF.trans hF,by ring⟩

end SevenEighths.InverseInitialCanonicalState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerEmpty
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerEmpty
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_zero_of_fresh_empty
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Point ι→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D B v θ H m c₁ c₂ θ₁ θ₂:ℝ)(hZ:0<Z)
    (hs:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
    (he:freshColumns p pool ω₁ (Z^(columnCenter D B v))=∅) :
    physicalBlock p hp hcop hg (pointSource pool S) w Ψ j marks
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0 := by
  unfold physicalBlock
  apply Finset.sum_eq_zero
  intro x hx
  have hv:=pointSource_valid pool S hdiv hf x hx
  have hleft:x.left⊆pool := by
    obtain ⟨s,hs,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨⟨N,M⟩,hNM,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).1).trans Finset.sdiff_subset
  have hω:ω₁ (columnRatio p x.left Z D B v)=0 := by
    by_contra hn
    rw [columnRatio_actual] at hn
    have hm:= (mem_freshColumns p pool ω₁ (Z^(columnCenter D B v)) x.left).mpr ⟨hleft,hn⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  have hW:clippedSource W₁ c₁ θ₁
      (relativeNorm (coordinates p x) Z D B v θ H 0 *
        relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 4)=0 := by
    by_contra hn
    have hh:=hs.1 x hx hn
    simp only [hω,star_zero] at hh
    exact zero_ne_one hh
  apply Finset.sum_eq_zero
  intro ρ hρ
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j marks _ _ Φ Z D m x hv ρ,
    physicalKernel_nominal _ _ Φ hZ D B v m θ H _ (coordinates_pos p hp x hv)]
  change w x*(_*(_*secondNormProfile _ _ _ _ _
    (relativeNorm (coordinates p x) Z D B v θ H)))=0
  simp only [secondNormProfile,hW,mul_zero,zero_mul,zero_div]

include hp hcop hg in

theorem physical_nonzero_clipping
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Point ι→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D B v θ H m c₁ c₂ θ₁ θ₂ a b η:ℝ)(hZ:1<Z)(hb:1≤b)
    (hω:Function.support ω₁⊆Set.Icc a b)
    (hs:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
    (ht:Real.log b≤3*η*Real.log Z)
    (hn:physicalBlock p hp hcop hg (pointSource pool S) w Ψ j marks
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m≠0) :
    0≤ max 0 (columnCenter D B v)-columnCenter D B v ∧
      max 0 (columnCenter D B v)-columnCenter D B v≤3*η := by
  apply freshColumns_initial_clipping_shift p hp pool ω₁ a b Z (columnCenter D B v) η hZ hb hω _ ht
  by_contra he
  have he':freshColumns p pool ω₁ (Z^(columnCenter D B v))=∅:=Finset.not_nonempty_iff_eq_empty.mp he
  exact hn (physicalBlock_zero_of_fresh_empty p hp hcop hg hpr pool S hdiv hf w Ψ j marks
    W₁ W₂ ω₁ ω₂ V Φ Z D B v θ H m c₁ c₂ θ₁ θ₂ (zero_lt_one.trans hZ) hs he')

end SevenEighths.InverseInitialEnergyCallerEmpty

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerFixedWindows
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerFixedWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseSecondChildWindows InverseSecondProfileUniform
local notation "Eis"=>ActualEisensteinCubic.O

theorem log_source_support (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W) :
    Function.support (CubicReflectionKernel.logSchwartz W a b ha hs hW)⊆
      Set.Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hh := hs hx
  change a≤Real.exp x ∧ Real.exp x≤b at hh
  have hl := Real.log_le_log ha hh.1
  have hu := Real.log_le_log (Real.exp_pos x) hh.2
  rw [Real.log_exp] at hl hu
  constructor
  · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]

theorem exists_actual_initial_windows
    (W₁ W₂:ℝ→ℂ)(a b bcap:ℝ)(ha:0<a)(hcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a b)(hs₂:Function.support W₂⊆Set.Icc a b)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (lo hi:Fin 4→ℝ)(hlo:∀i,0<lo i)(hhi:∀i,lo i≤hi i) :
    ∃(wFresh:𝓢(ℝ,ℂ))(V:Fin 6→𝓢(ℝ,ℂ))(M:Fin 6→ℝ)(af bf:ℝ),
      0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      (∀i,0≤M i) ∧ (∀i,HasCompactSupport (V i:ℝ→ℂ)) ∧
      (∀i,Function.support (V i)⊆Set.Icc (-M i) (M i)) ∧
      ∀{ι:Type*}[DecidableEq ι](p:ι→Eis)(_hp:∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
      (_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (ψ:Fin 4→ℝ→ℂ)(_hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
      (Z D B v θ H c₁ c₂ θ₁ θ₂:ℝ),0<Z→1≤ c₁→c₁≤bcap→1≤ c₂→c₂≤bcap→
      BlockSupport p (pointSource pool (windowSource p S ψ Z D B v θ H))
        W₁ W₂ wFresh wFresh (fun i=>V i) Z D B v θ H c₁ c₂ θ₁ θ₂ := by
  let m:=|Real.log a|+|Real.log b|
  obtain ⟨wFresh,V,M,af,bf,haf,hab,hwc,hws,hM,hVc,hVs,hw,hcut⟩ :=
    fixed_windows m bcap lo hi (fun _=>0) (by dsimp [m];positivity) hcap hlo hhi (by simp)
  refine ⟨wFresh,V,M,af,bf,haf,hab,hwc,hws,hM,hVc,hVs,?_⟩
  intro ι _ p hp _ pool S hdiv hf ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂ hZ hc₁ hb₁ hc₂ hb₂
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
  have hg₁ : Function.support g₁⊆Set.Icc (-m) m := log_source_support W₁ a b ha hs₁ hW₁
  have hg₂ : Function.support g₂⊆Set.Icc (-m) m := log_source_support W₂ a b ha hs₂ hW₂
  have hvalid : ∀x∈pointSource pool (windowSource p S ψ Z D B v θ H),Valid x :=
    pointSource_valid pool _ (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
      (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
  have hpos (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i,0< relativeNorm (coordinates p x) Z D B v θ H i :=
    relativeNorm_pos _ (coordinates_pos p hp x (hvalid x hx)) hZ D B v θ H
  have hblock (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i:Fin 4,relativeNorm (coordinates p x) Z D B v θ H (outerIndex i)∈Set.Icc (lo i) (hi i) :=
    fun i=>hψ i (windowSource_four_nonzero p pool S ψ Z D B v θ H hx i)
  refine ⟨?_,?_,?_⟩
  · intro x hx hn
    have he := hw g₁ hg₁ c₁ θ₁ _ _ _ hc₁ hb₁ (hblock x hx 0) (hblock x hx 2) (hpos x hx 4) ?_
    · rw [relative_column_left] at he
      rw [he,star_one]
    · change positiveSource g₁ c₁ θ₁
        (relativeNorm (coordinates p x) Z D B v θ H 0 *
          relativeNorm (coordinates p x) Z D B v θ H 2 *
          relativeNorm (coordinates p x) Z D B v θ H 4)≠0
      dsimp only [g₁]
      rw [positiveSource_logSchwartz W₁ a b ha hs₁ hW₁ (zero_lt_one.trans_le hc₁)
        (mul_pos (mul_pos (hpos x hx 0) (hpos x hx 2)) (hpos x hx 4))]
      exact hn
  · intro x hx hn
    have he := hw g₂ hg₂ c₂ θ₂ _ _ _ hc₂ hb₂ (hblock x hx 0) (hblock x hx 2) (hpos x hx 5) ?_
    · rwa [relative_column_right] at he
    · change positiveSource g₂ c₂ θ₂
        (relativeNorm (coordinates p x) Z D B v θ H 0 *
          relativeNorm (coordinates p x) Z D B v θ H 2 *
          relativeNorm (coordinates p x) Z D B v θ H 5)≠0
      dsimp only [g₂]
      rw [positiveSource_logSchwartz W₂ a b ha hs₂ hW₂ (zero_lt_one.trans_le hc₂)
        (mul_pos (mul_pos (hpos x hx 0) (hpos x hx 2)) (hpos x hx 5))]
      exact hn
  · intro x hx hl hr i
    have hl' : wFresh (relativeNorm (coordinates p x) Z D B v θ H 4)≠0 := by
      rw [relative_column_left]
      exact star_ne_zero.mp hl
    have hr' : wFresh (relativeNorm (coordinates p x) Z D B v θ H 5)≠0 := by
      rwa [relative_column_right]
    have he := hcut (relativeNorm (coordinates p x) Z D B v θ H) (fun _=>0)
      (by simp) (hblock x hx) hl' hr' i
    simpa only [add_zero,relativeLog] using he

end SevenEighths.InverseInitialEnergyCallerFixedWindows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialRetainedWindow
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedWindow
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerSourceMask InverseInitialQuotientGeometry InverseInitialClippedColumns
open InverseInitialCanonicalState InverseInitialEnergyCallerState FirstPassCubeLabels
local notation "O"=>ActualEisensteinCubic.O

theorem retained_window_bound_oai
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (lo hi:Fin 4→ℝ)(hlo:∀i,0<lo i)(hhi:∀i,lo i≤hi i)
    (cap gap eps U π:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hU:0≤U)(hπ:0<π)(K:ℕ):
    ∃degree:ℕ,∃Btree Tclip:ℝ,1≤Btree ∧ 0≤Tclip ∧
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
    ∀(ψ:Fin 4→ℝ→ℂ),(∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))→
    ∀(D B v θ H m r η τ:ℝ),0≤η→η≤gap/50→τ≤gap/50→
      (∀i,hi i≤Z^η)→Z^(-η)≤lo 1→Tclip≤3*η*Real.log Z→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→B-θ+2*η≤U→
      radialCenter m H θ D B≤4*η+τ→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤ c₁→c₁≤bcap→1≤ c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ (windowSource p S ψ Z D B v θ H))
        (w∘erasePoint) Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨fresh,Vlog,Mlog,af,bf,haf,hab,hfc,hfs,hM,hVc,hVs,hwindow⟩:=
    InverseInitialEnergyCallerFixedWindows.exists_actual_initial_windows
      W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ lo hi hlo hhi
  have hfs':Function.support (fresh:ℝ→ℂ)⊆Set.Icc af (max 1 bf):=by
    intro x hx
    have h:=hfs (subset_closure hx)
    exact ⟨h.1,h.2.trans (le_max_right _ _)⟩
  obtain ⟨J,Btree,hBtree,hbound⟩:=InverseInitialRetainedPhysical.retained_physical_bound
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ (fun i=>Vlog i) Mlog
    (fun i=>(Vlog i).smooth ⊤) hVc hM (fun i y hy=>abs_le.mpr (hVs i hy))
    fresh fresh af (max 1 bf) haf (le_max_left _ _) hfs' hfs' (fresh.smooth ⊤) (fresh.smooth ⊤)
    cap gap eps U π hcap hgap heps hU hπ K
  refine ⟨J,Btree,Real.log (max 1 bf),hBtree,Real.log_nonneg (le_max_left _ _),?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,hbound⟩:=hbound q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf ψ hψ
    D B v θ H m r η τ hη hηsmall hτ hhiZ hloZ hlog hprodj hprod hDeq hmargin₁ hmargin₂ hparent hR hrad
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hprimary:=InverseInitialRayAttachment.poolPrimary_primary F hFa
  let Sw:=windowSource p S ψ Z D B v θ H
  let Sc:=coprimeSource p Sw
  have hdivw:∀x∈Sw,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
  have hfw:∀x∈Sw,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
  have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdivw x (Finset.mem_filter.mp hx).1
  have hfc':∀x∈Sc,x.frequency≠0:=fun x hx=>hfw x (Finset.mem_filter.mp hx).1
  have hswhole:=hwindow p hp Finset.univ S hdiv hf ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂
    (zero_lt_one.trans hZp) hc₁ hbc₁ hc₂ hbc₂
  have hpoint:pointSource Finset.univ Sc⊆pointSource Finset.univ Sw:=by
    intro x hx
    obtain ⟨y,hy,hm⟩:=Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨y,(Finset.mem_filter.mp hy).1,hm⟩
  have hsupport:BlockSupport p (pointSource Finset.univ Sc) W₁ W₂ fresh fresh
      (fun i=>Vlog i) Z D B v θ H c₁ c₂ θ₁ θ₂:=
    ⟨fun x hx=>hswhole.1 x (hpoint hx),fun x hx=>hswhole.2.1 x (hpoint hx),
      fun x hx=>hswhole.2.2 x (hpoint hx)⟩
  rw [physicalBlock_coprimeSource p hp hcop hg hprimary Finset.univ _ hdivw hfw]
  by_cases hempty:physicalBlock p hp hcop hg (pointSource Finset.univ Sc) (w∘erasePoint) Ψ
      (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0
  · rw [hempty,norm_zero];positivity
  have hclip:= (InverseInitialEnergyCallerEmpty.physical_nonzero_clipping p hp hcop hg
    hprimary Finset.univ Sc hdivc hfc' (w∘erasePoint) Ψ (assignedElement assigned qelem)
    (primeMark (all\assigned) lists coeff) W₁ W₂ fresh fresh (fun i=>Vlog i) Φ
    Z D B v θ H m c₁ c₂ θ₁ θ₂ af (max 1 bf) η hZp (le_max_left _ _) hfs' hsupport hlog hempty).2
  have hqt:quotientSet p Sc⊆quotientSet p Sw:=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hn:∀t∈quotientSet p Sc,(t.absNorm:ℝ)≤Z^(B-θ+2*η):=by
    intro t ht
    exact retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
      (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZp)
      (hψ 0) (hψ 1) (hhiZ 0) hloZ hdiv t
      (window_quotient_subset_retained p S ψ Z D B v θ H (hqt ht))
  have hstates:∀t∈quotientSet p Sc,
      assignedElement assigned qelem*primaryGenerator t≠0 ∧ 0≤θ+v+2*η ∧ 0≤θ+H+2*η ∧
      0≤fullPunctureWidth Z t (assignedElement assigned qelem) ∧
      ‖eisEmbedding (assignedElement assigned qelem*primaryGenerator t)‖^2=
        Z^(fullPunctureWidth Z t (assignedElement assigned qelem)) ∧
      θ+H+2*η≤ cap ∧ max 0 (columnCenter D B v)+(θ+v+2*η)≤ cap ∧
      CanonicalMargins (max 0 (columnCenter D B v)+(θ+v+2*η)) (θ+H+2*η)
        (fullPunctureWidth Z t (assignedElement assigned qelem))
        (assignedCenter (all\assigned) z+η) gap:=by
    intro t ht
    have hs:=actual_window_state p hp hprimary S ψ lo hi hψ Z D B v θ H η hZp hη hhiZ hloZ
      hdiv hf all assigned hassigned qelem z al bl primeW hz hqe hprimeW hprimeLive hprodj (hqt ht)
      m r τ (2*gap) (2*gap) hDeq hmargin₁ hmargin₂ (by simp;positivity)
      (by simp only [min_self];linarith) (by simp only [min_self];linarith) hrad hclip
    simp only [min_self] at hs
    obtain ⟨hm,hN,hV,hM,hQ,he,hmargin,hF,hMr,hshift⟩:=hs
    refine ⟨hm,hV,hM,hQ,he,hMr.trans hparent,hF.trans hparent,?_⟩
    convert (preTransparency := .instances) hmargin using 1 <;> simp [columnCenter]
  apply hbound Z hZ Dpool hD (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK)
    lists Hslot coeff (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hHs hPs hac
    (assignedCenter (all\assigned) z+η) (by apply add_nonneg _ hη;exact Finset.sum_nonneg (fun i hi=>hz i (Finset.mem_sdiff.mp hi).1))
    hprod Ψ hΨ hperiod Sc hdivc hfc' (assignedElement assigned qelem) D B v θ H (B-θ+2*η) m η
    hR hη c₁ c₂ θ₁ θ₂ (zero_lt_one.trans_le hc₁) (zero_lt_one.trans_le hc₂) hsupport hn w
    (fun x hx=>hw x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    (idealRange (Z^(θ+v+2*η))) (nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)))
    (fun f hf=>mem_idealRange.mp hf) (Finset.Subset.refl _) ?_ ?_ hclip rfl hstates
  · intro k hk
    exact (child_ball_neg _ k).mpr hk
  · intro x hx
    exact InverseInitialCanonicalDomains.actual_window_domains p hp hcop hg (poolPrimary_odd F hFa)
      hprimary S hdiv hf ψ lo hi hψ Z D B v θ H η (zero_lt_one.trans hZp) hhiZ x hx _

end SevenEighths.InverseInitialRetainedWindow

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseInitialRetainedWindow.retained_window_bound_oai := @OAI.SevenEighths.InverseInitialRetainedWindow.retained_window_bound_oai
