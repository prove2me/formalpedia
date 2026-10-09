-- Prove2me | solution 1 for OAI.SevenEighths.InverseInitialEnergyCallerPhysical.actual_physical_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:00:11.525991+00:00
-- url     : https://prove2.me/submissions/aa3e9eeb-5794-4e3f-8c39-d2e47df61e30

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B016
import Theorems.Thm_OAI_SevenEighths_InverseInitialEnergyCallerIntegral_actual_common_integral_bound

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

theorem primeProductNorm_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (S T : Finset ι) (hd : Disjoint S T) :
    primeProductNorm p (S ∪ T) = primeProductNorm p S * primeProductNorm p T := by
  simp only [primeProductNorm, Finset.prod_union hd, map_mul, norm_mul, mul_pow]

end FirstPassCubeLabels

open scoped BigOperators Classical

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

section
open FourierBridge FirstPassCubeLabels

lemma source_le_profileSourceBound (g : 𝓢(ℝ, ℂ)) (J i : ℕ) (hi : i ≤ J) :
    (SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g ≤
      profileSourceBound g J := by
  unfold profileSourceBound
  apply Finset.single_le_sum (s := Finset.range (J + 1)) (a := i)
    (f := fun k : ℕ => (SchwartzMap.seminorm ℝ 0 k) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower k) g)
  · intro j hj
    positivity
  · exact Finset.mem_range.mpr (by omega)

end

open FirstPassCubeLabels

end JointLogSeparation

open scoped BigOperators

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

lemma logPhase_hasDerivAt (t x : ℝ) :
    HasDerivAt (logPhase t) (phaseDerivative t * logPhase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (phaseDerivative t)).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  have he (y : ℝ) : Complex.exp (phaseDerivative t * (y : ℂ)) = logPhase t y := by
    unfold phaseDerivative logPhase
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  simpa only [mul_comm] using h

lemma logPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logPhase t) = fun x => phaseDerivative t ^ n * logPhase t x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun y => phaseDerivative t ^ n * logPhase t y) x =
        phaseDerivative t ^ n * (phaseDerivative t * logPhase t x) from
      ((logPhase_hasDerivAt t x).const_mul _).deriv]
    simp only [pow_succ]
    ring

lemma phaseDerivative_norm (t : ℝ) : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  simp only [phaseDerivative, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_of_nonneg Real.pi_pos.le]

lemma logPhase_iteratedFDeriv_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (logPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logPhase_iteratedDeriv]
  simp only [norm_mul, norm_pow, phaseDerivative_norm, logPhase_norm, mul_one]

lemma derivativeSeminormSum_nonneg (g : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    0 ≤ derivativeSeminormSum g k n := by unfold derivativeSeminormSum; positivity

lemma seminorm_le_derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n i : ℕ) (hi : i ≤ n) :
    (SchwartzMap.seminorm ℝ k i) g ≤ derivativeSeminormSum g k n := by
  apply Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => (SchwartzMap.seminorm ℝ k j) g) (a := i)
  · intro j hj; positivity
  · exact Finset.mem_range.mpr (by omega)

theorem frequencyTwist_seminorm_bound (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (derivativeSeminormSum_nonneg _ _ _))
  intro x
  have hh := norm_iteratedFDeriv_mul_le (logPhase_temperate t).1 (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hfun : (frequencyTwist g t : ℝ → ℂ) = fun x => logPhase t x * g x := by
    funext x; exact frequencyTwist_apply g t x
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (logPhase t) x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 * Real.pi * ‖t‖)^i * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) g x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [logPhase_iteratedFDeriv_norm]
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hp : (2 * Real.pi * ‖t‖)^i ≤ (1 + 2 * Real.pi * ‖t‖)^n := by
        calc
          _ ≤ (1 + 2 * Real.pi * ‖t‖)^i := by gcongr; linarith
          _ ≤ _ := pow_le_pow_right₀ (by
            have hc : 0 ≤ 2 * Real.pi * ‖t‖ := by positivity
            linarith) hin
      have hs := (SchwartzMap.le_seminorm ℝ k (n-i) g x).trans
        (seminorm_le_derivativeSeminormSum g k n (n-i) (Nat.sub_le n i))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hs (by positivity)
        (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

theorem frequencyTwist_seminorm_polynomial (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      ((2 : ℝ)^n * (1 + 2 * Real.pi)^n * derivativeSeminormSum g k n) * (1 + ‖t‖)^n := by
  have hsum := derivativeSeminormSum_nonneg g k n
  have hp : 1 + 2 * Real.pi * ‖t‖ ≤ (1 + 2 * Real.pi) * (1 + ‖t‖) := by
    nlinarith [Real.pi_pos, norm_nonneg t]
  calc
    _ ≤ (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n :=
      frequencyTwist_seminorm_bound g t k n
    _ ≤ (2 : ℝ)^n * ((1 + 2 * Real.pi) * (1 + ‖t‖))^n * derivativeSeminormSum g k n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

lemma twistSourceBound_nonneg (g : 𝓢(ℝ, ℂ)) (K : ℕ) : 0 ≤ twistSourceBound g K := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))

theorem profileSourceBound_frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) (K : ℕ) :
    profileSourceBound (frequencyTwist g t) K ≤ twistSourceBound g K * (1 + ‖t‖)^K := by
  unfold profileSourceBound twistSourceBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ K := Finset.mem_range_succ_iff.mp hi
  have hb := add_le_add (frequencyTwist_seminorm_polynomial g t 0 i)
    (frequencyTwist_seminorm_polynomial g t (volume : Measure ℝ).integrablePower i)
  have hn : 0 ≤ (2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))
  calc
    _ ≤ ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
        (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i)) *
          (1 + ‖t‖)^i := by convert (preTransparency := .instances) hb using 1 ; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hin) hn

end JointLogSeparation

open scoped BigOperators Classical

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles
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

open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
namespace SecondPassIntegration
open JointLogSeparation FourierBridge

lemma logPhase_conjugate (t x : ℝ) : star (logPhase t x) = logPhase (-t) x := by
  unfold logPhase
  simp only [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  push_cast
  ring

end SecondPassIntegration

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.PrincipalNormalization
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
open FirstPassCubeLabels (primeProductNorm b0Label jLabel cubeRadical)
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem secondChildColumn_zero_of_mask_label_mem (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hmf : m*f ∈ Ideal.span {p i}) :
    secondChildColumn p hp hcop hg Ψ m f y H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hmf with hm|hf
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m=0 := by
      simp only [rowCoprimeMask,if_pos (show ∃ i∈S,m ∈ Ideal.span {p i} from ⟨i,hi,hm⟩)]
    simp only [secondChildColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S f=0 := by
      simp only [rowCoprimeMask,if_pos (show ∃ i∈S,f ∈ Ideal.span {p i} from ⟨i,hi,hf⟩)]
    have hr := FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S f hz
    simp only [secondChildColumn,hr,zero_pow (by decide : (4 : ℕ) ≠ 0),mul_zero,zero_mul]

theorem fixedChildRow_restore_killed_pool (F B : Finset ι) (Ψ : O →* ℂ)
    (m f y : O) (H : Finset ι → ℂ) (hB : ∀ i∈B,m*f ∈ Ideal.span {p i}) :
    fixedChildRow p hp hcop hg (F\B) Ψ m H f y = fixedChildRow p hp hcop hg F Ψ m H f y := by
  unfold fixedChildRow
  apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
  intro S hS hn
  have hd : ¬ Disjoint B S := by
    intro hd
    apply hn
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) hi,
      fun hiB => Finset.disjoint_left.mp hd hiB hi⟩
  obtain ⟨i,hiB,hiS⟩ := Finset.not_disjoint_iff.mp hd
  exact secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f y H S i hiS (hB i hiB)

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Marks
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem primeSlot_priority (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (A ∪ B) = primeSlot L a A + primeSlot L a (B \ A) := by
  unfold primeSlot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hA : p ∈ A <;> by_cases hB : p ∈ B <;> simp [hA, hB]

theorem primeMark_priority (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (A ∪ B) =
      ∑ J ∈ I.powerset, primeMark J L a A * primeMark (I \ J) L a (B \ A) := by
  unfold primeMark
  simp_rw [primeSlot_priority]
  exact Finset.prod_add _ _ I

theorem primeSlot_residual_list (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (B \ A) = primeSlot (L \ A) a B := by
  simp only [primeSlot, Finset.sum_ite_mem]
  congr 1
  ext p
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

omit [DecidableEq σ] in
theorem primeMark_residual_lists (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (B \ A) = primeMark I (fun i => L i \ A) a B := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact primeSlot_residual_list _ _ _ _

end

end SevenEighths.InverseMoment

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

theorem secondChildSum_marked_canonical
    (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k
      (fun U => primeMark slots lists a (A ∪ U) * W (primeProductNorm p U / X)) =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
      finiteCanonicalMarkedRow p hp hcop hg (F \ V) Ψ (m * r)
        (c * e * ∏ i ∈ V, p i) (d * e * k)
        (slots \ J) (fun i => lists i \ (A ∪ V)) a W (X / primeProductNorm p V) := by
  unfold secondChildSum finiteCanonicalMarkedRow fixedChildRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N hN
  have hd : Disjoint V N := Finset.disjoint_left.mpr (fun i hi hn =>
    (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hn)).2 hi)
  have hn : primeProductNorm p (V ∪ N) / X = primeProductNorm p N / (X / primeProductNorm p V) := by
    rw [primeProductNorm_union p V N hd]
    simp only [div_div_eq_mul_div]
    ring
  have hmark := primeMark_priority slots lists a (A ∪ V) N
  simp only [primeMark_residual_lists] at hmark
  simp only [secondChildColumn, ← Finset.union_assoc, hn]
  rw [hmark]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_restore_pool
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg (pool \ B) Ψ m f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X :=
  fixedChildRow_restore_killed_pool p hp hcop hg pool B Ψ m f k _ hB

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_restore_lists
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots (fun i => lists i \ B) a W X =
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  by_cases hd : Disjoint B U
  · have he : U \ B = U := Finset.sdiff_eq_self_of_disjoint hd.symm
    simp only [secondChildColumn, ← primeMark_residual_lists, he]
  · obtain ⟨i, hiB, hiU⟩ := Finset.not_disjoint_iff.mp hd
    rw [secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB),
      secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB)]

theorem secondChildSum_marked_fixed_pool
    (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k
      (fun U => primeMark slots lists a (A ∪ U) * W (primeProductNorm p U / X)) =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (m * r)
        (c * e * ∏ i ∈ V, p i) (d * e * k)
        (slots \ J) (fun i => lists i \ A) a W (X / primeProductNorm p V) := by
  rw [secondChildSum_marked_canonical]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  have hV (i : ι) (hi : i ∈ V) : (m * r) * (c * e * ∏ j ∈ V, p j) ∈ Ideal.span {p i} :=
    Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hi) (c * e)) (m * r))
  rw [finiteCanonicalMarkedRow_restore_pool p hp hcop hg F V Ψ (m * r)
    (c * e * ∏ i ∈ V, p i) (d * e * k) _ _ _ _ _ hV]
  have hlists : (fun i => lists i \ (A ∪ V)) = (fun i => (lists i \ A) \ V) := by
    funext i
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [hlists]
  exact finiteCanonicalMarkedRow_restore_lists p hp hcop hg F V Ψ (m * r)
    (c * e * ∏ i ∈ V, p i) (d * e * k) _ _ _ _ _ hV

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

theorem descent_profile_identity {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak : ι → ℝ)
    (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (he : ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t : ℝ, (∏ i, V i (y i) * logPhase t (ak i * y i)) * b t) :
    ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * g₁ (∑ i, a₁ i * y i) * g₂ (∑ i, a₂ i * y i) *
        paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 g₁) (𝓕 g₂) b (t₁, t₂, t₃) *
          (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
            logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) := by
  intro y
  let P : ℂ := ∏ i, V i (y i)
  let x₁ : ℝ := ∑ i, a₁ i * y i
  let x₂ : ℝ := ∑ i, a₂ i * y i
  let xk : ℝ := ∑ i, ak i * y i
  have hphase (t : ℝ) (a : ι → ℝ) :
      (∏ i, logPhase t (a i * y i)) = logPhase t (∑ i, a i * y i) :=
    (logPhase_sum Finset.univ t (fun i => a i * y i)).symm
  have hk' : P * paperRadialFourier W (R * Real.exp xk) =
      ∫ t : ℝ, P * logPhase t xk * b t := by
    simpa only [Finset.prod_mul_distrib, hphase, P, xk] using he y
  have hprod (t₁ t₂ t₃ : ℝ) :
      (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
        logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) =
      P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk := by
    simp only [Finset.prod_mul_distrib, hphase, P, x₁, x₂, xk]
  simp only [hprod, tripleCoefficient]
  have hinner (t₁ t₂ : ℝ) :
      (∫ t₃ : ℝ, (𝓕 g₁) t₁ * ((𝓕 g₂) t₂ * b t₃) *
        (P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk)) =
      ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [hk', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t₃
    ring
  simp_rw [hinner]
  have hmid (t₁ : ℝ) :
      (∫ t₂ : ℝ, ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk))) =
      (logPhase t₁ x₁ * (𝓕 g₁) t₁) * g₂ x₂ *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [schwartz_logPhase_inversion g₂ x₂, ← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with t₂
    ring
  simp_rw [hmid]
  rw [integral_mul_const, integral_mul_const, ← schwartz_logPhase_inversion]
  dsimp only [P, x₁, x₂, xk]
  ring

theorem tripleCoefficient_weighted_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : Frequency =>
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) := by
  have hi (b : 𝓢(ℝ, ℂ)) : Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖b t‖) := by
    have he : (𝓕 (𝓕⁻ b) : 𝓢(ℝ, ℂ)) = b := by simp
    simpa only [he] using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J
  convert (preTransparency := .instances) (hi b₁).mul_prod ((hi b₂).mul_prod (hi b₃)) using 1
  funext t
  simp only [tripleCoefficient, norm_mul]
  ring

theorem tripleCoefficient_weighted_integral (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ t : Frequency,
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) =
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₁ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₂ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) := by
  have he (t : Frequency) :
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖ =
      ((1 + ‖t.1‖)^J * ‖b₁ t.1‖) *
        (((1 + ‖t.2.1‖)^J * ‖b₂ t.2.1‖) * ((1 + ‖t.2.2‖)^J * ‖b₃ t.2.2‖)) := by
    simp only [tripleCoefficient, norm_mul]
    ring
  simp_rw [he]
  simp only [Measure.volume_eq_prod]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₁ t‖)
    (fun t : ℝ × ℝ => ((1 + ‖t.1‖)^J * ‖b₂ t.1‖) * ((1 + ‖t.2‖)^J * ‖b₃ t.2‖))]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₂ t‖) (fun t : ℝ => (1 + ‖t‖)^J * ‖b₃ t‖)]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.DescentHeight
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
noncomputable section

theorem frequencyTwist_fourier_moment (J : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (frequencyTwist g θ)) t‖) ≤
        C * (1 + ‖θ‖)^(J + (volume : Measure ℝ).integrablePower) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let D := twistSourceBound g K
  have hD : 0 ≤ D := twistSourceBound_nonneg g K
  let C := (2 : ℝ)^J * (coefficientMomentBound 0 D + coefficientMomentBound J D)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (add_nonneg
    (coefficientMomentBound_nonneg 0 D hD) (coefficientMomentBound_nonneg J D hD))
  refine ⟨C, hC, ?_⟩
  intro θ
  let H := (1 + ‖θ‖)^K
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hs : ∀ i ≤ K,
      (SchwartzMap.seminorm ℝ 0 i) (frequencyTwist g θ) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) (frequencyTwist g θ) ≤ D * H := by
    intro i hi
    exact (source_le_profileSourceBound (frequencyTwist g θ) K i hi).trans
      (profileSourceBound_frequencyTwist g θ K)
  have hh := uniform_fourier_one_plus_moment (frequencyTwist g θ) J 1 (D * H)
    (by norm_num) (mul_nonneg hD hH) (fun i hi => by simpa only [one_mul] using hs i hi)
  have hlin (j : ℕ) : coefficientMomentBound j (D * H) = coefficientMomentBound j D * H := by
    unfold coefficientMomentBound
    ring
  simpa only [one_mul, hlin, add_mul, C, H, K, mul_assoc, mul_add] using hh

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.WindowFourier
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem coordinate_fourier_inversion (g : ι → 𝓢(ℝ, ℂ)) (y : ι → ℝ) :
    (∏ i, g i (y i)) = ∫ t : ι → ℝ, coordinateDensity g t * coordinatePhase t y := by
  simp only [coordinateDensity, coordinatePhase, ← Finset.prod_mul_distrib]
  have hp := integral_fintype_prod_volume_eq_prod (E := fun _ : ι => ℝ)
    (fun (i : ι) (t : ℝ) => (𝓕 (g i) : 𝓢(ℝ, ℂ)) t * logPhase t (y i))
  rw [hp]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [mul_comm] using schwartz_logPhase_inversion (g i) (y i)

theorem coordinate_density_weighted_integrable (g : ι → 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ι → ℝ => (∏ i, (1 + ‖t i‖)^J) * ‖coordinateDensity g t‖) := by
  have hi (i : ι) := AnalyticBridge.schwartz_fourier_one_plus_integrable (g i) J
  convert (preTransparency := .instances) Integrable.fintype_prod hi using 1
  funext t
  simp only [coordinateDensity, norm_prod, Finset.prod_mul_distrib]

theorem coordinate_density_weighted_integral (g : ι → 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ t : ι → ℝ, (∏ i, (1 + ‖t i‖)^J) * ‖coordinateDensity g t‖) =
      ∏ i, ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (g i)) t‖ := by
  simp only [coordinateDensity, norm_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_volume_eq_prod (E := fun _ : ι => ℝ)
    (fun i t => (1 + ‖t‖)^J * ‖(𝓕 (g i)) t‖)

theorem profileMode_coordinate_separation (g : ι → 𝓢(ℝ, ℂ))
    (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ) (t : Frequency) :
    profileMode (fun i => g i) a₁ a₂ ak y t =
      ∫ u : ι → ℝ, coordinateDensity g u * pureProfileMode a₁ a₂ ak y t u := by
  simp only [profileMode, pureProfileMode, Finset.prod_mul_distrib]
  simp only [← mul_assoc]
  rw [integral_mul_const, integral_mul_const, integral_mul_const]
  have he := coordinate_fourier_inversion g y
  simp only [coordinatePhase] at he
  rw [← he]

 theorem pureProfileMode_norm (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ)
    (t : Frequency) (u : ι → ℝ) : ‖pureProfileMode a₁ a₂ ak y t u‖ = 1 := by
  simp [pureProfileMode, norm_prod,  logPhase_norm]

theorem fullProfileDensity_weighted_integrable (g : ι → 𝓢(ℝ, ℂ))
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun p : Frequency × (ι → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 * ‖fullProfileDensity g b₁ b₂ b₃ p‖) := by
  convert (preTransparency := .instances) (tripleCoefficient_weighted_integrable b₁ b₂ b₃ J).mul_prod
    (coordinate_density_weighted_integrable g J) using 1
  funext p
  simp only [tripleHeight, coordinateHeight, fullProfileDensity, norm_mul]
  ring

theorem fullProfileDensity_weighted_integral (g : ι → 𝓢(ℝ, ℂ))
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ p : Frequency × (ι → ℝ),
      tripleHeight J p.1 * coordinateHeight J p.2 * ‖fullProfileDensity g b₁ b₂ b₃ p‖) =
      (∫ t : Frequency, tripleHeight J t * ‖tripleCoefficient b₁ b₂ b₃ t‖) *
      (∏ i, ∫ u : ℝ, (1 + ‖u‖)^J * ‖(𝓕 (g i)) u‖) := by
  have he (p : Frequency × (ι → ℝ)) :
      tripleHeight J p.1 * coordinateHeight J p.2 * ‖fullProfileDensity g b₁ b₂ b₃ p‖ =
        (tripleHeight J p.1 * ‖tripleCoefficient b₁ b₂ b₃ p.1‖) *
        (coordinateHeight J p.2 * ‖coordinateDensity g p.2‖) := by
    simp only [fullProfileDensity, norm_mul]
    ring
  simp_rw [he]
  simp only [Measure.volume_eq_prod]
  rw [integral_prod_mul (fun t : Frequency => tripleHeight J t * ‖tripleCoefficient b₁ b₂ b₃ t‖)
    (fun u : ι → ℝ => coordinateHeight J u * ‖coordinateDensity g u‖)]
  simp only [coordinateHeight]
  rw [coordinate_density_weighted_integral g J]

theorem profile_integral_coordinate_absorption (g : ι → 𝓢(ℝ, ℂ))
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (a₁ a₂ ak y : ι → ℝ) :
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) *
        profileMode (fun i => g i) a₁ a₂ ak y (t₁,t₂,t₃)) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : ι → ℝ,
      fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
        pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u := by
  apply integral_congr_ae
  filter_upwards with t₁
  apply integral_congr_ae
  filter_upwards with t₂
  apply integral_congr_ae
  filter_upwards with t₃
  rw [profileMode_coordinate_separation, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [fullProfileDensity]
  ring

lemma logPhase_scaled_coordinate (t a y : ℝ) : logPhase t (a*y) = logPhase (a*t) y := by
  unfold logPhase
  congr 1
  push_cast
  ring

theorem pureProfileMode_height (a₁ a₂ ak y : ι → ℝ) (t : Frequency) (u : ι → ℝ) :
    pureProfileMode a₁ a₂ ak y t u = ∏ i, logPhase (profileHeight a₁ a₂ ak t u i) (y i) := by
  apply Finset.prod_congr rfl
  intro i hi
  simp only [profileHeight, logPhase_add_frequency, logPhase_scaled_coordinate]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ProfileIntegral
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma full_density_integrable (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) :
    Integrable (fullProfileDensity g b₁ b₂ b₃) := by
  have hc : Continuous (fullProfileDensity g b₁ b₂ b₃) := by
    unfold fullProfileDensity coordinateDensity tripleCoefficient
    fun_prop
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  simpa only [tripleHeight,coordinateHeight,pow_zero,Finset.prod_const_one,mul_one,one_mul] using
    fullProfileDensity_weighted_integrable g b₁ b₂ b₃ 0

lemma full_density_mode_integrable (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (a₁ a₂ ak y : ι → ℝ) :
    Integrable (fun p : Frequency × (ι → ℝ) => fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak y p.1 p.2) := by
  have hc : Continuous (fun p : Frequency × (ι → ℝ) => pureProfileMode a₁ a₂ ak y p.1 p.2) := by
    unfold pureProfileMode logPhase
    fun_prop
  exact (full_density_integrable g b₁ b₂ b₃).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => (pureProfileMode_norm a₁ a₂ ak y p.1 p.2).le))

theorem full_density_mode_fubini (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (a₁ a₂ ak y : ι → ℝ) :
    (∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak y p.1 p.2) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : ι → ℝ,
      fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
        pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u := by
  let f : Frequency × (ι → ℝ) → ℂ := fun p => fullProfileDensity g b₁ b₂ b₃ p *
    pureProfileMode a₁ a₂ ak y p.1 p.2
  have hf : Integrable f (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using full_density_mode_integrable g b₁ b₂ b₃ a₁ a₂ ak y
  change (∫ p, f p) = _
  rw [Measure.volume_eq_prod, integral_prod _ hf]
  have ht : Integrable (fun t : Frequency => ∫ u, f (t,u)) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hf.integral_prod_left
  rw [Measure.volume_eq_prod, integral_prod _ ht]
  apply integral_congr_ae
  filter_upwards [ht.prod_right_ae] with t₁ ht₁
  simpa only [Measure.volume_eq_prod] using integral_prod (fun t : ℝ×ℝ => ∫ u, f ((t₁,t.1,t.2),u)) ht₁

theorem full_density_finite_sum {κ : Type*} (s : Finset κ)
    (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) (a₁ a₂ ak : ι → ℝ)
    (c : κ → ℂ) (y : κ → ι → ℝ) :
    (∑ k ∈ s, c k * ∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak (y k) p.1 p.2) =
    ∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      ∑ k ∈ s, c k * pureProfileMode a₁ a₂ ak (y k) p.1 p.2 := by
  simp only [← integral_const_mul]
  rw [← integral_finsetSum s (fun k hk =>
    (full_density_mode_integrable g b₁ b₂ b₃ a₁ a₂ ak (y k)).const_mul (c k))]
  apply integral_congr_ae
  filter_upwards with p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
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

lemma secondPoissonProfile_log (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    secondPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) =
      secondNormProfile W₁ W₂ Φ V R q := by
  have hleft : (∑ i, secondLeftSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 4) := by
    simp [Fin.sum_univ_succ,secondLeftSlope]; ring
  have hright : (∑ i, secondRightSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 5) := by
    simp [Fin.sum_univ_succ,secondRightSlope]; ring
  have hker : (∑ i, secondKernelSlope i * Real.log (q i)) =
      Real.log (q 3) - (Real.log (q 1)+Real.log (q 2)+Real.log (q 2)+Real.log (q 4)+Real.log (q 5)) := by
    simp [Fin.sum_univ_succ,secondKernelSlope]; ring
  unfold secondPoissonProfile secondNormProfile
  rw [hleft,hright,hker]
  simp only [Real.exp_add,Real.exp_sub,Real.exp_log (hq _)]
  have hk : R * (q 3/(q 1*q 2*q 2*q 4*q 5)) = R*q 3/(q 1*(q 2)^2*q 4*q 5) := by ring
  rw [hk]
  simp only [Fin.prod_univ_succ,secondRootWindows,inverseNormWindow,inverseRootWindow,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,Real.exp_log (hq _),Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,  Fin.val_mk]
  ((try simp ) <;> norm_num )
  ring

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma second_mode_split (y : Fin 6 → ℝ) (t : Frequency) (u : Fin 6 → ℝ) :
    pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t u =
      secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u) y *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 4) (y 4) *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 5) (y 5) := by
  rw [pureProfileMode_height]
  simp only [Fin.prod_univ_succ, secondOuterPhase]
  simp only [Fin.succ,  Fin.val_mk]
  ((try simp ) <;> norm_num )
  ring

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

open InverseMoment

theorem fourier_phase_shift (f : ℝ → ℂ) (θ t : ℝ) :
    (𝓕 (fun y => logPhase θ y * f y)) t = (𝓕 f) (t-θ) := by
  simp only [Real.fourier_eq', logPhase, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translate (f : ℝ → ℂ) (ρ t : ℝ) :
    (𝓕 (fun y => f (y+ρ))) t = logPhase t ρ * (𝓕 f) t := by
  have h := congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) f ρ) t
  change _ = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t at h
  have h' : (𝓕 (fun y => f (y+ρ))) t = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t := by
    simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, Function.comp_def, innerₗ_apply_apply] using h
  rw [h']
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, logPhase]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    (𝓕 (fun y => logPhase θ y * f (y+ρ))) t =
      logPhase (t-θ) ρ * (𝓕 f) (t-θ) := by
  rw [fourier_phase_shift, fourier_translate]

theorem norm_fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    ‖(𝓕 (fun y => logPhase θ y * f (y+ρ))) t‖ = ‖(𝓕 f) (t-θ)‖ := by
  rw [fourier_translated_twist, norm_mul, logPhase_norm, one_mul]

theorem translated_twist_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J *
        ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ≤
        C*(1+‖θ‖)^(momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseMoment.frequencyTwist_fourier_moment J g
  refine ⟨C, hC, ?_⟩
  intro ρ θ
  have he (t : ℝ) : ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖ =
      ‖(𝓕 (frequencyTwist g θ)) t‖ := by
    rw [norm_fourier_translated_twist, congrFun (SchwartzMap.fourier_coe _) t]
    have hf : (frequencyTwist g θ : ℝ → ℂ) = fun y => logPhase θ y * g y := by
      funext y
      exact frequencyTwist_apply g θ y
    rw [hf, fourier_phase_shift]
  simp_rw [he]
  exact ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable _ _, hb θ⟩

end SevenEighths.InverseClippingProfiles

end

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

theorem initial_marked_child (F V A : Finset ι) (Ψ : O →* ℂ) (j t d h : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ N∈(F\V).powerset,
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>primeMark slots lists a (A∪V∪U)*
          W (primeProductNorm p (V∪U)/X)) N) =
    ∑ J∈slots.powerset,primeMark J lists a (A∪V)*
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (slots\J) (fun i=>lists i\A) a W (X/primeProductNorm p V) := by
  simpa only [secondChildSum,one_mul,←Finset.union_assoc] using
    secondChildSum_marked_fixed_pool p hp hcop hg F V A Ψ j t 1 1 d h slots lists a W X

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_ne_zero (S : Finset ι) : sourceIdeal p S≠0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_union (S T : Finset ι) (hst : Disjoint S T) :
    sourceIdeal p (S∪T)=sourceIdeal p S*sourceIdeal p T := by
  simp only [sourceIdeal,Finset.prod_union hst,Ideal.span_singleton_mul_span_singleton]

omit [DecidableEq ι] in
theorem source_prime_dvd (S : Finset ι) (i : ι) (hi : i∈S) :
    (sourcePrime p i).val∣sourceIdeal p S := by
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact Finset.dvd_prod_of_mem p hi

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment

namespace SevenEighths.InverseInitialProfile

theorem fourier_clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    (𝓕 (clippedTwist g c θ)) t = sourceDensity g c θ t := by
  rw [SchwartzMap.fourier_coe]
  have he : (clippedTwist g c θ : ℝ → ℂ) =
      fun y => logPhase θ y * g (y + Real.log c) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translated_twist]
  rfl

theorem sourceDensity_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
        C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseClippingProfiles.translated_twist_moment_uniform g J
  refine ⟨C, hC, ?_⟩
  intro c θ
  simpa only [InverseClippingProfiles.fourier_translated_twist, sourceDensity,
    SchwartzMap.fourier_coe] using hb (Real.log c) θ

theorem clipped_log_source (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c : ℝ} (hc : 0 < c) (θ y : ℝ) :
    clippedTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) c θ y =
      clippedSource W c θ (Real.exp y) := by
  simp only [clippedTwist_apply, CubicReflectionKernel.logSchwartz_apply,
    clippedSource, Real.log_exp, Real.exp_add, Real.exp_log hc]
  rw [mul_comm (Real.exp y) c]

theorem familyDensity_weighted_integrable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) := by
  convert (preTransparency := .instances) (InverseMoment.fullProfileDensity_weighted_integrable g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ J).const_mul
      (Real.exp (-3*L)) using 1
  funext p
  simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  ring

theorem familyDensity_weighted_integral
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Frequency × (Fin 6 → ℝ),
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) =
    Real.exp (-3*L) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
      ∏ i, ∫ u : ℝ, (1+‖u‖)^J * ‖(𝓕 (g i)) u‖ := by
  have he (p : Frequency × (Fin 6 → ℝ)) :
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖ =
      Real.exp (-3*L) * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (clippedTwist g₁ c₁ θ₁))
          (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p‖) := by
    simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  simp only [fourier_clippedTwist]
  ring

theorem family_common_measure
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ c₁ c₂ θ₁ θ₂ L : ℝ, 0 ≤ L →
      (∀ y : Fin 6 → ℝ,
        logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
          ∫ p : Frequency × (Fin 6 → ℝ),
            familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  have hb : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  obtain ⟨C₃, hC₃, hsep⟩ := paperRadialFourier_log_separation_envelope
    Φ (secondRootWindows V) secondKernelSlope M hM hb A J
  obtain ⟨C₁, hC₁, h₁⟩ := sourceDensity_moment_uniform g₁ J
  obtain ⟨C₂, hC₂, h₂⟩ := sourceDensity_moment_uniform g₂ J
  let D : ℝ := ∏ i, ∫ u : ℝ, (1+‖u‖)^J *
    ‖(𝓕 (secondRootSchwartz V hV hS i)) u‖
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun u => by positivity))
  refine ⟨C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, _, hm, _⟩ := hsep R hR
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ L hL
  refine ⟨?_, familyDensity_weighted_integrable _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope R b₃ he y
    have habs := profile_integral_coordinate_absorption (secondRootSchwartz V hV hS)
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      secondLeftSlope secondRightSlope secondKernelSlope y
    have hid' : logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
        (Real.exp (-3*L) : ℂ) *
          ∫ p : Frequency × (Fin 6 → ℝ),
            fullProfileDensity (secondRootSchwartz V hV hS)
              (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2 := by
      unfold logFamilyProfile
      rw [hid]
      congr 1
      rw [full_density_mode_fubini]
      simpa only [profileMode, secondRootSchwartz, rootSchwartz_apply] using habs
    rw [hid', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold familyDensity
    ring
  · rw [familyDensity_weighted_integral]
    have h1 := (h₁ c₁ θ₁).2
    have h2 := (h₂ c₂ θ₂).2
    have h12 := mul_le_mul h1 h2 (integral_nonneg (fun _ => by positivity))
      (mul_nonneg hC₁ (by positivity))
    have hm0 : 0 ≤ (1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖ := by positivity
    have h123 := mul_le_mul h12 hm hm0 (by positivity)
    have h123D := mul_le_mul_of_nonneg_right h123 hD
    have hnorm : Real.exp (-3*L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have heq : (1+R)^A * (Real.exp (-3*L) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) =
      Real.exp (-3*L) * (((∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖)) *
        ((1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) := by ring
    change (1+R)^A * (_ * _ * _ * _ * D) ≤ _
    rw [heq]
    exact (mul_le_mul_of_nonneg_left h123D (Real.exp_pos _).le).trans
      ((mul_le_of_le_one_left (by positivity) hnorm).trans_eq (by ring))

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

theorem initial_normalization_scalar {Z : ℝ} (hZ : 0 < Z) (κ η : ℝ) :
    Z^(κ+3*η) * Real.exp (-3*(η*Real.log Z)) = Z^κ := by
  have he : Real.exp (-3*(η*Real.log Z)) = Z^(-3*η) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he, ← Real.rpow_add hZ]
  congr 1
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

theorem normalizedProfile_eq_family (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (θ₁ θ₂ R L : ℝ)
    (y : Fin 6 → ℝ) :
    normalizedProfile (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ V R L y =
      logFamilyProfile (CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁)
        (CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂)
        Φ V c₁ c₂ θ₁ θ₂ R L y := by
  unfold normalizedProfile logFamilyProfile secondPoissonProfile
  rw [clipped_log_source W₁ a b ha hs₁ hW₁ hc₁,
    clipped_log_source W₂ a b ha hs₂ hW₂ hc₂]

theorem fresh_profile_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i)
    (hw₁ : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1)
    (hw₂ : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1)
    (hV : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 → ∀ i, V i (Real.log (x i)) = 1) :
    (Real.exp (-3*L) : ℂ) * secondNormProfile W₁ W₂ Φ (fun _ _ => 1) R x =
      (w₁ (x 4)*w₂ (x 5)) * normalizedProfile W₁ W₂ Φ V R L (fun i => Real.log (x i)) := by
  unfold normalizedProfile
  rw [secondPoissonProfile_log W₁ W₂ Φ V R x hx]
  by_cases h1 : W₁ (x 0*x 2*x 4) = 0
  · simp only [secondNormProfile, h1, mul_zero, zero_mul, zero_div]
  by_cases h2 : W₂ (x 0*x 2*x 5) = 0
  · simp only [secondNormProfile, h2, mul_zero, zero_mul, zero_div]
  have hv := hV (by rw [hw₁ h1]; exact one_ne_zero) (by rw [hw₂ h2]; exact one_ne_zero)
  simp only [secondNormProfile, hv, hw₁ h1, hw₂ h2, Finset.prod_const_one, one_mul]

theorem relativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    {Z : ℝ} (hZ : 0 < Z) (D B v θ H : ℝ) :
    ∀ i, 0 < relativeNorm q Z D B v θ H i :=
  secondRelativeNorm_pos q hq _ _ _ _ _
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _)

theorem initial_kernel_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hw₁ : W₁ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1)
    (hw₂ : W₂ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1)
    (hV : w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 → ∀ i, V i (relativeLog q Z D B v θ H i) = 1) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        normalizedProfile W₁ W₂ Φ V (Z^(radialCenter m H θ D B))
          (η*Real.log Z) (relativeLog q Z D B v θ H) := by
  rw [physicalKernel_nominal W₁ W₂ Φ hZ D B v m θ H q hq]
  have hs := fresh_profile_restore W₁ W₂ w₁ w₂ Φ V (Z^(radialCenter m H θ D B))
    (η*Real.log Z) (relativeNorm q Z D B v θ H)
    (relativeNorm_pos q hq hZ D B v θ H) hw₁ hw₂ hV
  have hn : ((Z^(prefactorCenter m D B θ) : ℝ) : ℂ) =
      (Z^(prefactorCenter m D B θ+3*η) : ℝ) * (Real.exp (-3*(η*Real.log Z)) : ℂ) := by
    rw [← Complex.ofReal_mul, initial_normalization_scalar hZ]
  rw [show relativeLog q Z D B v θ H =
    (fun i => Real.log (relativeNorm q Z D B v θ H i)) by rfl]
  rw [hn, mul_assoc]
  simpa only [mul_assoc, relativeNorm] using congrArg
    (fun z : ℂ => (Z^(prefactorCenter m D B θ+3*η) : ℝ) * z) hs

theorem initial_physical_family_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    let g := secondRootSchwartz V hV hS
    let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
    let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z D B v m θ H η : ℝ, 0 < Z → 0 ≤ η*Real.log Z →
      ∃ b₃ : 𝓢(ℝ, ℂ), ∀ c₁ c₂ θ₁ θ₂ : ℝ, 0 < c₁ → 0 < c₂ →
      PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂ ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ∧
      (1+Z^(radialCenter m H θ D B))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hsep⟩ := family_common_measure
    (CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁)
    (CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂)
    Φ V M hV hS hM hbox A J
  refine ⟨C, hC, ?_⟩
  intro Z D B v m θ H η hZ hL
  obtain ⟨b₃, hb₃⟩ := hsep (Z^(radialCenter m H θ D B)) (Real.rpow_pos_of_pos hZ _)
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ hc₁ hc₂
  obtain ⟨he, hi, hbound⟩ := hb₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) hL
  refine ⟨?_, hi, hbound⟩
  intro w₁ w₂ q hq hw₁ hw₂ hcut
  rw [initial_kernel_restore _ _ w₁ w₂ Φ V hZ D B v m θ H η q hq hw₁ hw₂ hcut,
    normalizedProfile_eq_family W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V hc₁ hc₂, he]

end SevenEighths.InverseInitialProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerFamily
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialEnergyCallerFamily
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem common_killed (G E V : Finset ι) (_hE : E⊆G) (j d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∀ i∈G,(j*t)*(d*∏ k∈V,p k)∈Ideal.span {p i} := by
  intro i hi
  by_cases hiE : i∈E
  · have he : d∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp (source_prime_dvd p E i hiE))
      rw [←hd]
      exact Ideal.subset_span (Set.mem_singleton d)
    have hh := (Ideal.span {p i}).mul_mem_left ((j*t)*(∏ k∈V,p k)) he
    convert (preTransparency := .instances) hh using 1 ; ring
  · have hit : i∈G\E := Finset.mem_sdiff.mpr ⟨hi,hiE⟩
    have he : t∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp (source_prime_dvd p (G\E) i hit))
      rw [←ht]
      exact Ideal.subset_span (Set.mem_singleton t)
    have hh := (Ideal.span {p i}).mul_mem_left (j*(d*∏ k∈V,p k)) he
    convert (preTransparency := .instances) hh using 1 ; ring

theorem marked_child_original_lists (F G E V : Finset ι) (hE : E⊆G)
    (Ψ : Eis →* ℂ) (j d t h : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E))
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ N∈(F\V).powerset,
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>primeMark slots lists a (G∪V∪U)*W (primeProductNorm p (V∪U)/X)) N) =
    ∑ J∈slots.powerset,primeMark J lists a (G∪V)*
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (slots\J) lists a W (X/primeProductNorm p V) := by
  rw [initial_marked_child p hp hcop hg F V G Ψ j t d h slots lists a W X]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_restore_lists p hp hcop hg F G Ψ (j*t)
    (d*∏ i∈V,p i) (d*h) (slots\J) lists a W (X/primeProductNorm p V)
    (common_killed p G E V hE j d t hd ht)]

omit [DecidableEq σ] in
theorem normalized_child_uniform
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (G E V : Finset ι) (d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Eisˣ, d=(u:Eis)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
        (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ),
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
        (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
        (primaryGenerator (sourceIdeal p E)*((u:Eis)^5*h)) slots lists a W X := by
  have hgen : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  obtain ⟨u,hu⟩ := generator_eq_unit_primary (sourceIdeal p E) d hd hgen
  refine ⟨u,hu,?_⟩
  intro F Ψ j h slots lists a W X
  obtain ⟨v,hv,hcol⟩ := initial_poisson_child_normalized p hp hcop hg hpr G E V Ψ j d t h hd ht
  have huv : v=u := by
    apply Units.val_injective
    exact mul_right_cancel₀ hgen (hv.symm.trans hu)
  subst v
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro N hN
  exact hcol _ N

theorem fresh_initial_split_fixed_family
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (G E V : Finset ι) (hE : E⊆G) (d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Eisˣ, d=(u:Eis)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
        (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ),
      (∑ N∈(F\V).powerset,
        secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
          (fun U=>primeMark slots lists a (G∪V∪U)*W (primeProductNorm p U/X)) N) =
      ∑ J∈slots.powerset,primeMark J lists a (G∪V)*
        finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
          (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
          (primaryGenerator (sourceIdeal p E)*((u:Eis)^5*h)) (slots\J) lists a W X := by
  obtain ⟨u,hu,hnorm⟩ := normalized_child_uniform p hp hcop hg hpr G E V d t hd ht (σ:=σ)
  refine ⟨u,hu,?_⟩
  intro F Ψ j h slots lists a W X
  have hV : primeProductNorm p V≠0 := (primeProductNorm_pos p hp V).ne'
  have hx : primeProductNorm p V*X/primeProductNorm p V=X := by
    field_simp
  have he := marked_child_original_lists p hp hcop hg F G E V hE Ψ j d t h hd ht
    slots lists a W (primeProductNorm p V*X)
  rw [hx] at he
  calc
    _ = ∑ N∈(F\V).powerset,
        secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
          (fun U=>primeMark slots lists a (G∪V∪U)*
            W (primeProductNorm p (V∪U)/(primeProductNorm p V*X))) N := by
      apply Finset.sum_congr rfl
      intro N hN
      have hdN : Disjoint V N := Finset.disjoint_left.mpr (by
        intro i hiV hiN
        exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hiN)).2 hiV)
      simp only [secondChildColumn]
      rw [primeProductNorm_union p V N hdN]
      rw [mul_div_mul_left _ _ hV]
    _ = _ := by
      rw [he]
      apply Finset.sum_congr rfl
      intro J hJ
      rw [hnorm F Ψ j h (slots\J) lists a W X]

end SevenEighths.InverseInitialEnergyCallerFamily

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

theorem canonical_pair_mode (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) (z : Frequency × (Fin 6→ℝ)) :
    barePair p hp hcop hg hpr Ψ j σ x ρ *
      (star (ω₁ (columnRatio p x.left Z D B v))*ω₂ (columnRatio p x.right Z D B v)) *
      pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
        (relativeLog (coordinates p x) Z D B v θ H) z.1 z.2 =
      canonicalPairMode p hp hcop hg hpr Ψ j σ ω₁ ω₂ Z D B v θ H x ρ z := by
  rw [second_mode_split]
  simp only [canonicalPairMode,barePair,canonicalColumn,secondChildColumn,childLogTest,
    star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,relativeLog,
    relative_column_left,relative_column_right,mul_one]
  ring

theorem family_density_finite_sum {κ : Type*} (s : Finset κ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ)) (c₁ c₂ θ₁ θ₂ L : ℝ)
    (c : κ→ℂ) (y : κ→Fin 6→ℝ) :
    (∑ k∈s,c k*∫ z : Frequency × (Fin 6→ℝ),
      familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2) =
    ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z *
      ∑ k∈s,c k*pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2 := by
  simp only [familyDensity,mul_assoc,integral_const_mul]
  have he := full_density_finite_sum s g (𝓕 (clippedTwist g₁ c₁ θ₁))
    (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ secondLeftSlope secondRightSlope secondKernelSlope c y
  calc
    _ = (Real.exp (-3*L):ℂ)*∑ k∈s,c k*∫ z : Frequency × (Fin 6→ℝ),
        fullProfileDensity g (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ z *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2 := by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro k hk;ring
    _ = _ := by rw [he]

theorem physicalBlock_integral
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ)
    (hid : PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂)
    (source : Finset (Point ι)) (hs : ∀ x∈source,Valid x)
    (w : Point ι→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hω₁ : ∀ x∈source,clippedSource W₁ c₁ θ₁
      (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 4)≠0 → star (ω₁ (columnRatio p x.left Z D B v))=1)
    (hω₂ : ∀ x∈source,clippedSource W₂ c₂ θ₂
      (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 5)≠0 → ω₂ (columnRatio p x.right Z D B v)=1)
    (hcut : ∀ x∈source,star (ω₁ (columnRatio p x.left Z D B v))≠0 →
      ω₂ (columnRatio p x.right Z D B v)≠0 → ∀ i,V i (relativeLog (coordinates p x) Z D B v θ H i)=1) :
    physicalBlock p hp hcop hg source w Ψ j σ (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*
      ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
        canonicalBlock p hp hcop hg hpr source w Ψ j σ ω₁ ω₂ Z D B v θ H z := by
  let S := source ×ˢ (Finset.univ : Finset SecondRayIndex)
  let c := fun a : Point ι × SecondRayIndex => w a.1*barePair p hp hcop hg hpr Ψ j σ a.1 a.2 *
    (star (ω₁ (columnRatio p a.1.left Z D B v))*ω₂ (columnRatio p a.1.right Z D B v))
  let y := fun a : Point ι × SecondRayIndex => relativeLog (coordinates p a.1) Z D B v θ H
  have he := family_density_finite_sum S g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) c y
  have hpnt (x : Point ι) (hx : x∈source) (ρ : SecondRayIndex) :
      w x*physicalTerm p hp hcop hg Ψ j σ (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m x ρ =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*c (x,ρ)*
        ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y (x,ρ)) z.1 z.2 := by
    rw [physicalTerm_extracted p hp hcop hg hpr Ψ j σ _ _ Φ Z D m x (hs x hx) ρ]
    rw [hid (fun r=>star (ω₁ r)) ω₂ (coordinates p x) (coordinates_pos p hp x (hs x hx))
      (hω₁ x hx) (hω₂ x hx) (hcut x hx)]
    dsimp only [c,y,barePair]
    rw [relative_column_left,relative_column_right]
    ring
  have hsumeq : physicalBlock p hp hcop hg source w Ψ j σ
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*
        ∑ a∈S,c a*∫ z : Frequency × (Fin 6→ℝ),
          familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y a) z.1 z.2 := by
    simp only [physicalBlock,S,Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [hpnt x hx ρ]
    ring
  rw [hsumeq,he]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  simp only [S,Finset.sum_product,canonicalBlock,c,y]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mul_assoc (w x),mul_assoc (w x),canonical_pair_mode]

open InverseInitialOverlap InverseInitialPoissonBridge CanonicalQuadraticSieve

end SevenEighths.InverseInitialPhysicalMeasure

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerModes
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialPhysicalMeasure SevenEighths.InverseInitialKernelBridge
open SevenEighths.InverseInitialEnergyCallerFamily SevenEighths.InverseInitialProfile
namespace SevenEighths.InverseInitialEnergyCallerModes
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonicalColumn_marked_sum
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Point ι) (hE : x.divisor⊆x.common)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (Z D B v : ℝ) :
    (∑ N∈(F\x.overlap).powerset,
      canonicalColumn p hp hcop hg hpr Ψ j (primeMark slots lists a) x h
        (fun A=>W (columnRatio p A Z D B v)) N) =
      ∑ J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*quotient p x)
          (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
          (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:Eis)^5*h))
          (slots\J) lists a W (Z^(columnCenter D B v)) := by
  have hgen (A : Finset ι) : primaryGenerator (sourceIdeal p A)≠0 := by
    rw [sourceIdeal_gen p hp hpr A]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hd : Ideal.span {primaryGenerator (sourceIdeal p x.divisor)}=sourceIdeal p x.divisor :=
    (primaryGenerator_spec _ (hgen _)).1
  have ht : Ideal.span {quotient p x}=sourceIdeal p (x.common\x.divisor) :=
    (primaryGenerator_spec _ (hgen _)).1
  obtain ⟨u,hu,hsplit⟩ := fresh_initial_split_fixed_family p hp hcop hg hpr
    x.common x.divisor x.overlap hE (primaryGenerator (sourceIdeal p x.divisor))
    (quotient p x) hd ht (σ:=σ)
  have hu1 : u=1 := by
    apply Units.val_injective
    apply mul_right_cancel₀ (hgen x.divisor)
    simpa only [Units.val_one,one_mul] using hu.symm
  subst u
  have he := hsplit F Ψ j ((unitSector p hp hpr x:Eis)^5*h) slots lists a W
    (Z^(columnCenter D B v))
  simp only [Units.val_one,one_pow,one_mul] at he
  convert (preTransparency := .instances) he using 1
  · apply Finset.sum_congr rfl
    intro N hN
    simp only [canonicalColumn,primaryGenerator_mul,sourceIdeal_gen p hp hpr x.overlap,
      secondChildColumn,columnRatio_actual,Finset.union_assoc]
  · rfl

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourcePoint_outer_phase (x : Source (ι:=ι) 0) (N M : Finset ι)
    (height : Fin 6→ℝ) (Z D B v θ H : ℝ) :
    secondOuterPhase height (relativeLog (coordinates p (sourcePoint x N M)) Z D B v θ H) =
    secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H) := by
  have hc₀ : coordinates p (sourcePoint x N M) 0=coordinates p (sourcePoint x ∅ ∅) 0 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  have hc₁ : coordinates p (sourcePoint x N M) 1=coordinates p (sourcePoint x ∅ ∅) 1 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  have hc₂ : coordinates p (sourcePoint x N M) 2=coordinates p (sourcePoint x ∅ ∅) 2 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  have hc₃ : coordinates p (sourcePoint x N M) 3=coordinates p (sourcePoint x ∅ ∅) 3 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  simp [secondOuterPhase,relativeLog,relativeNorm,secondRelativeNorm,hc₀,hc₁,hc₂,hc₃]

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem sourcePoint_unitSector
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Source (ι:=ι) 0) (N M : Finset ι) :
    unitSector p hp hpr (sourcePoint x N M)=unitSector p hp hpr (sourcePoint x ∅ ∅) := by
  have hgen : primaryGenerator (sourceIdeal p x.divisor)≠0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  apply Units.val_injective
  apply mul_right_cancel₀ hgen
  exact (unitSector_spec p hp hpr (sourcePoint x N M)).symm.trans
    (unitSector_spec p hp hpr (sourcePoint x ∅ ∅))

theorem canonicalPairMode_rectangle
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Source (ι:=ι) 0) (hE : x.divisor⊆x.common)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ) (ρ : SecondRayIndex)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) :
    let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
    (∑ N∈(F\x.overlap).powerset,∑ M∈(F\x.overlap).powerset,
      canonicalPairMode p hp hcop hg hpr Ψ j (primeMark slots lists a) ω₁ ω₂
        Z D B v θ H (sourcePoint x N M) ρ z) =
    (outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
      secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)) *
    (star (markedModeColumn p hp hcop hg hpr F (secondRayMinus Ψ ρ) j x.frequency x
        slots lists a (childLogTest ω₁ (-height 4)) Z D B v) *
      markedModeColumn p hp hcop hg hpr F (secondRayPlus Ψ ρ) j (-x.frequency) x
        slots lists a (childLogTest ω₂ (height 5)) Z D B v) := by
  dsimp only
  let x₀ := sourcePoint x ∅ ∅
  have hpoint (N M : Finset ι) :
      canonicalPairMode p hp hcop hg hpr Ψ j (primeMark slots lists a) ω₁ ω₂
        Z D B v θ H (sourcePoint x N M) ρ z =
      (outerCoefficient p hp hcop hg Ψ j x₀ ρ *
        secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2)
          (relativeLog (coordinates p x₀) Z D B v θ H)) *
      star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j (primeMark slots lists a) x₀ x.frequency
        (fun A=>childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4)
          (columnRatio p A Z D B v)) N) *
      canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j (primeMark slots lists a) x₀ (-x.frequency)
        (fun A=>childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5)
          (columnRatio p A Z D B v)) M := by
    unfold InverseInitialPhysicalMeasure.canonicalPairMode
    dsimp only
    rw [sourcePoint_outer_phase p x N M
      (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) Z D B v θ H]
    simp only [canonicalColumn]
    simp only [sourcePoint_unitSector p hp hpr x N M]
    simp only [outerCoefficient,sourcePoint,divisor,quotient,x₀]
  simp_rw [hpoint,←Finset.mul_sum]
  rw [←Finset.sum_mul,←Finset.mul_sum,←star_sum]
  have hleft := canonicalColumn_marked_sum p hp hcop hg hpr x₀ hE F (secondRayMinus Ψ ρ) j x.frequency
      slots lists a (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4)) Z D B v
  have hright := canonicalColumn_marked_sum p hp hcop hg hpr x₀ hE F (secondRayPlus Ψ ρ) j (-x.frequency)
      slots lists a (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5)) Z D B v
  dsimp only [x₀,sourcePoint] at hleft hright ⊢
  rw [hleft,hright]
  simp only [markedModeColumn,sourcePoint]
  ring

end SevenEighths.InverseInitialEnergyCallerModes

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

theorem canonicalBlock_rows
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hE : ∀ x∈S,x.divisor⊆x.common) (w : Source (ι:=ι) 0→ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (j : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) :
    canonicalBlock p hp hcop hg hpr (pointSource F S) (w ∘ erasePoint) Ψ j
      (primeMark slots lists a) ω₁ ω₂ Z D B v θ H z =
      ∑ x∈S,∑ ρ : SecondRayIndex,w x*rowMode p hp hcop hg hpr F Ψ j
        slots lists a ω₁ ω₂ Z D B v θ H x ρ z := by
  unfold canonicalBlock
  rw [pointSource_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Function.comp_apply,erase_sourcePoint]
  calc
    _ = ∑ N∈(F\x.overlap).powerset,∑ ρ : SecondRayIndex,∑ M∈(F\x.overlap).powerset,
        w x*InverseInitialPhysicalMeasure.canonicalPairMode p hp hcop hg hpr Ψ j
          (primeMark slots lists a) ω₁ ω₂ Z D B v θ H (sourcePoint x N M) ρ z := by
      apply Finset.sum_congr rfl
      intro N hN
      exact Finset.sum_comm
    _ = ∑ ρ : SecondRayIndex,∑ N∈(F\x.overlap).powerset,∑ M∈(F\x.overlap).powerset,
        w x*InverseInitialPhysicalMeasure.canonicalPairMode p hp hcop hg hpr Ψ j
          (primeMark slots lists a) ω₁ ω₂ Z D B v θ H (sourcePoint x N M) ρ z := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      simp_rw [←Finset.mul_sum]
      rw [canonicalPairMode_rectangle p hp hcop hg hpr x (hE x hx) F Ψ j
        slots lists a ω₁ ω₂ Z D B v θ H ρ z]
      rfl

theorem physicalBlock_rectangular_common_measure
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ)
    (hid : PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂)
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hE : ∀ x∈S,x.divisor⊆x.common) (hf : ∀ x∈S,x.frequency≠0)
    (w : Source (ι:=ι) 0→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (j : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hsupport : BlockSupport p (pointSource F S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂) :
    physicalBlock p hp hcop hg (pointSource F S) (w ∘ erasePoint) Ψ j (primeMark slots lists a)
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
    (Z^(prefactorCenter m D B θ+3*η):ℝ)*
      ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
        (∑ x∈S,∑ ρ : SecondRayIndex,w x*rowMode p hp hcop hg hpr F Ψ j
          slots lists a ω₁ ω₂ Z D B v θ H x ρ z) := by
  rw [physicalBlock_integral p hp hcop hg hpr W₁ W₂ Φ V g g₁ g₂ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid (pointSource F S) (pointSource_valid F S hE hf)
    (w ∘ erasePoint) Ψ j (primeMark slots lists a) ω₁ ω₂
    hsupport.1 hsupport.2.1 hsupport.2.2]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [canonicalBlock_rows p hp hcop hg hpr F S hE w Ψ j slots lists a ω₁ ω₂ Z D B v θ H z]

end SevenEighths.InverseInitialEnergyCallerSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerPhysical
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerPhysical
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation
open InverseInitialQuotientGeometry InverseInitialClippedColumns
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_physical_block_bound_oai
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(V:Fin 6→ℝ→ℂ)(M:Fin 6→ℝ)
    (hV:∀i,ContDiff ℝ ∞ (V i))(hS:∀i,HasCompactSupport (V i))
    (hM:∀i,0≤M i)(hbox:∀i y,V i y≠0→|y|≤M i)
    (J N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R m η:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hη:0≤η*Real.log Z)(c₁ c₂ θ₁ θ₂:ℝ)(_hc₁:0<c₁)(_hc₂:0<c₂)
      (_hsupport:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A:ℝ)(_hA:0≤A)
      (_hmoment:∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2) ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2)),
      ‖physicalBlock p hp hcop hg (pointSource pool S) (w ∘ erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(prefactorCenter m D B θ+3*η+F+R+π)*A*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) := by
  obtain ⟨Ce,hCe,he⟩ := InverseInitialEnergyCallerIntegral.actual_common_integral_bound N U π hU hπ
  obtain ⟨Cp,hCp,hprofile⟩ := initial_physical_family_common_measure
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox 0 J
  refine ⟨Ce*(Cp+1),mul_pos hCe (by linarith),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R m η hZ hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F A hA hmoment
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  obtain ⟨b₃,hb₃⟩ := hprofile Z D B v m θ H η hZp hη
  obtain ⟨hid,hint,hprofileBound⟩ := hb₃ c₁ c₂ θ₁ θ₂ hc₁ hc₂
  let g := secondRootSchwartz V hV hS
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a₀ b₀ ha₀ hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a₀ b₀ ha₀ hs₂ hW₂
  have hb := he p hp hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn w hw labels rows hlabels hneg hchild F A hA J
    g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) hmoment
  have hprof : (∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
      tripleHeight J z.1*coordinateHeight J z.2*
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z‖)≤
      (Cp+1)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) := by
    simp only [pow_zero,one_mul] at hprofileBound
    exact hprofileBound.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  rw [physicalBlock_rectangular_common_measure p hp hcop hg hpr W₁ W₂ Φ V g g₁ g₂ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid pool S hdiv hf w Ψ j slots lists a ω₁ ω₂ hsupport]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZp _)]
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZp.le _)).trans
  calc
    _≤Z^(prefactorCenter m D B θ+3*η)*
      (Ce*Z^(F+R+π)*A*((Cp+1)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J))) := by gcongr
    _=_ := by
      have hexp : Z^(prefactorCenter m D B θ+3*η+F+R+π)=
          Z^(prefactorCenter m D B θ+3*η)*Z^(F+R+π) := by
        rw [show prefactorCenter m D B θ+3*η+F+R+π=
          (prefactorCenter m D B θ+3*η)+(F+R+π) by ring,Real.rpow_add hZp]
      rw [hexp]
      ring

end SevenEighths.InverseInitialEnergyCallerPhysical

end

end OAI
end

theorem solution.{u_3, u_4} : type_of% @OAI.SevenEighths.InverseInitialEnergyCallerPhysical.actual_physical_block_bound_oai.{u_3, u_4} := @OAI.SevenEighths.InverseInitialEnergyCallerPhysical.actual_physical_block_bound_oai.{u_3, u_4}
