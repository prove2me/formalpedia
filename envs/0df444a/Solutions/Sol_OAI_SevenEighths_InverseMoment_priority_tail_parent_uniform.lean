-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.priority_tail_parent_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:30:15.766338+00:00
-- url     : https://prove2.me/submissions/2c0dc3b9-f852-4258-ae4f-9c3f3ca53ab3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

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

end

theorem prime_product_moebius
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
      (-1 : ℂ) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one, Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
    have hcop : IsCoprime (P i) (∏ j ∈ S, P j) := by
      apply IsCoprime.prod_right
      intro j hj
      apply Ideal.isCoprime_of_isMaximal
      exact hinj.ne (by intro h; subst j; exact hi hj)
    rw [Finset.prod_insert hi, hcop.isRelPrime.moebius_mul,
      (hprime i).irreducible.moebius_eq, Int.cast_mul, Int.cast_neg,
      Int.cast_one, ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.RadialFourier
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

namespace EisensteinSchwartzPoisson

open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap

theorem polynomial_tail_majorant (A : ℕ) (K T q B f : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (htail : T ≤ K * q) (hbound : (1 + K * q) ^ (A + 2) * f ≤ B) :
    f ≤ (B / ((min 1 K) ^ 2 * (1 + T) ^ A)) * ((1 + q) ^ 2)⁻¹ := by
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hm1 : min 1 K ≤ 1 := min_le_left _ _
  have hmK : min 1 K ≤ K := min_le_right _ _
  have hbase : min 1 K * (1 + q) ≤ 1 + K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hmK hq]
  have htwo : (min 1 K) ^ 2 * (1 + q) ^ 2 ≤ (1 + K * q) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hpow : (1 + T) ^ A ≤ (1 + K * q) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hden : ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2 ≤
      (1 + K * q) ^ (A + 2) := by
    have hh := mul_le_mul hpow htwo (by positivity) (by positivity)
    rw [pow_add]
    nlinarith
  have hprod : f * (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) ≤ B := by
    calc
      _ = (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) * f := mul_comm _ _
      _ ≤ (1 + K * q) ^ (A + 2) * f := mul_le_mul_of_nonneg_right hden hf
      _ ≤ B := hbound
  have hraw := (le_div_iff₀ (show 0 < ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2
      by positivity)).mpr hprod
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem paperRadialFourier_lattice_summable_norm (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))

theorem paperRadialFourier_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
        (∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound (A + 2)
  refine ⟨s, C * (eisensteinCauchyMass + 1), by
    have := eisensteinCauchyMass_nonneg
    positivity, ?_⟩
  intro W K T hK hT
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + T) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hD : 0 < D := by dsimp [D]; positivity
  let S := {h : O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  have hp (h : S) :
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    exact polynomial_tail_majorant A K T _ B _ hK hT (sq_nonneg _)
      (norm_nonneg _) h.property (hb W _ (by positivity))
  have hmajor : Summable (fun h : S => (B / D) *
      ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
    (eisenstein_cauchy_summable.subtype S).mul_left (B / D)
  have hs : Summable (fun h : S =>
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : S, (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / D) * ∑' h : S, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / D) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype S) (div_nonneg hB hD.le)
    _ ≤ (B / D) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, D]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
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

namespace ActualEisensteinCubic

theorem primeSubsetGenerator_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    primeSubsetGenerator P E ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  change (∏ i ∈ E, P i) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))

open ConcreteTraceCRT

open ConcreteTraceCRT EisensteinSchwartzPoisson

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
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
namespace ActualEisensteinCubic

theorem activeExponent_ne_zero {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : activeExponent S T i ≠ 0 := by
  unfold activeExponent
  split_ifs <;> decide

theorem activeExponent_lt_six {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : activeExponent S T i < 6 := by
  unfold activeExponent
  split_ifs <;> decide

theorem finiteSexticRow_activeSupport {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset α) (u : O) :
    finiteSexticRow (activePrimes P S T) (fun i => hgood i.val) (activeExponent S T) u =
      star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by
  classical
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hpow5 (i : α) :
      (canonicalSextic (P i) (hgood i) ^ 5) (Ideal.Quotient.mk (P i) u) =
        star (canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) u)) := by
    rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0)]
    rw [canonicalSextic_conj_as_row_label]
    ring
  unfold finiteSexticRow activePrimes activeExponent
  let f : α → ℂ := fun i =>
    (canonicalSextic (P i) (hgood i) ^ (if i ∈ S \ T then 5 else 1))
      (Ideal.Quotient.mk (P i) u)
  change (∏ i : activeSupport S T, f i.val) = _
  rw [Finset.prod_coe_sort (s := activeSupport S T) (f := f)]
  change (∏ i ∈ (S \ T) ∪ (T \ S),
    (canonicalSextic (P i) (hgood i) ^ (if i ∈ S \ T then 5 else 1))
      (Ideal.Quotient.mk (P i) u)) = _
  rw [Finset.prod_union hd]
  simp only [finiteSquarefreeRow, star_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [if_pos hi, hpow5]
  · apply Finset.prod_congr rfl
    intro i hi
    have hnot : i ∉ S \ T := fun h => Finset.disjoint_left.mp hd h hi
    rw [if_neg hnot, pow_one]

open ConcreteTraceCRT EisensteinSchwartzPoisson

end ActualEisensteinCubic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RayCharacters
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

namespace FirstCauchyArithmetic

section
open ActualEisensteinCubic CoprimeMobiusExtension

theorem supportMobius_sq {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    supportMobius P S * supportMobius P S = 1 := by
  rw [supportMobius, prime_product_moebius P hprime hinj, ← mul_pow]
  norm_num

end

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem family_prime_dvd_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    P i ∣ ∏ j ∈ S, P j ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hd⟩ := ((family_prime P i).dvd_finsetProd_iff P).mp h
    have he : P i = P j := associated_iff_eq.mp
      ((family_prime P i).associated_of_dvd (family_prime P j) hd)
    exact hinj he ▸ hj
  · exact fun hi => Finset.dvd_prod_of_mem P hi

theorem family_product_injective {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) : Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T h
  change (∏ i ∈ S, P i) = (∏ i ∈ T, P i) at h
  ext i
  rw [← family_prime_dvd_product_iff P hinj S i, h, family_prime_dvd_product_iff P hinj T i]

end FirstCauchyArithmetic

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

theorem row_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    finiteSquarefreeRow P hg S (∏ j ∈ B, a j) =
      ∏ j ∈ B, finiteSquarefreeRow P hg S (a j) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [finiteSquarefreeRow]
  | @insert j B hj ih =>
    simp only [Finset.prod_insert hj, finiteSquarefreeRow_mul, ih]

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

theorem mask_mul (a b : O) :
    rowCoprimeMask P S (a * b) = rowCoprimeMask P S a * rowCoprimeMask P S b := by
  simp only [← row_sixth P hg S, finiteSquarefreeRow_mul, mul_pow]

theorem mask_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    rowCoprimeMask P S (∏ j ∈ B, a j) = ∏ j ∈ B, rowCoprimeMask P S (a j) := by
  rw [← row_sixth P hg S, row_prod, ← Finset.prod_pow]
  simp only [row_sixth]

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ChildTransfer
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

open scoped BigOperators Classical

section
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem commonProduct_mask
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (U G : Finset ι) :
    rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) =
      if Disjoint U G then 1 else 0 := by
  by_cases hd : Disjoint U G
  · rw [if_pos hd, FirstPassCubeLabels.mask_prod _ hg U G p]
    apply Finset.prod_eq_one
    intro j hj
    have hh : ¬ ∃ i ∈ U, p j ∈ Ideal.span {p i} := by
      rintro ⟨i, hi, hpi⟩
      have hij : i ≠ j := fun he => Finset.disjoint_left.mp hd hi (he ▸ hj)
      exact (prime_generator_not_mem_of_ne (Ideal.span {p i}) (Ideal.span {p j})
        (fun he => hij (hinj he)) (p j) rfl) hpi
    simp [rowCoprimeMask, hh]
  · rw [if_neg hd]
    obtain ⟨i, hiU, hiG⟩ := Finset.not_disjoint_iff.mp hd
    have hh : ∃ j ∈ U, (∏ i ∈ G, p i) ∈ Ideal.span {p j} :=
      ⟨i, hiU, Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hiG)⟩
    simp [rowCoprimeMask, hh]

theorem sum_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, A U) =
      ∑ U ∈ F.powerset, rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) * A U := by
  have hsub : (F \ G).powerset ⊆ F.powerset := Finset.powerset_mono.mpr Finset.sdiff_subset
  calc
    _ = ∑ U ∈ (F \ G).powerset,
        rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) * A U := by
      apply Finset.sum_congr rfl
      intro U hU
      have hd : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hG =>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hi)).2 hG)
      rw [commonProduct_mask p hg hinj U G, if_pos hd, one_mul]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro U hUF hUG
      have hd : ¬ Disjoint U G := by
        intro hd
        apply hUG
        apply Finset.mem_powerset.mpr
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hUF) hi,
          fun hG => Finset.disjoint_left.mp hd hi hG⟩
      rw [commonProduct_mask p hg hinj U G, if_neg hd, zero_mul]

omit [DecidableEq ι] in
theorem secondInputCoefficient_fixed_mask (Ψ : O →* ℂ) (m g c d : O)
    (H : Finset ι → ℂ) (U : Finset ι) :
    secondInputCoefficient p hg Ψ (m*g) c d H U =
      rowCoprimeMask (fun i => Ideal.span {p i}) U g * secondInputCoefficient p hg Ψ m c d H U := by
  rw [secondInputCoefficient, FirstPassCubeLabels.mask_mul _ hg U m g]
  unfold secondInputCoefficient
  ring

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem sum_pair_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset, A U V) =
      ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
        rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) *
        rowCoprimeMask (fun i => Ideal.span {p i}) V (∏ i ∈ G, p i) * A U V := by
  rw [sum_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  rw [sum_remove_common_pool p hg hinj F G, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  ring

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
lemma star_mask (P : ι → Ideal O) (S : Finset ι) (a : O) :
    star (rowCoprimeMask P S a) = rowCoprimeMask P S a := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem input_pair_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
      if Disjoint U V then
        star (supportMobius (fun i => Ideal.span {p i}) U * secondInputCoefficient p hg Ψ₁ m c d H₁ U) *
        (supportMobius (fun i => Ideal.span {p i}) V * secondInputCoefficient p hg Ψ₂ m c d H₂ V) * K U V
      else 0) =
    ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
      if Disjoint U V then
        star (supportMobius (fun i => Ideal.span {p i}) U *
          secondInputCoefficient p hg Ψ₁ (m * ∏ i ∈ G, p i) c d H₁ U) *
        (supportMobius (fun i => Ideal.span {p i}) V *
          secondInputCoefficient p hg Ψ₂ (m * ∏ i ∈ G, p i) c d H₂ V) * K U V
      else 0 := by
  rw [sum_pair_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [if_pos hd, if_pos hd, secondInputCoefficient_fixed_mask,
      secondInputCoefficient_fixed_mask]
    simp only [star_mul, star_mask]
    ring
  · simp [hd]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
theorem secondMaskQuotient_spec (E G : Finset ι) (hEG : E ⊆ G) :
    (∏ i ∈ G, p i) = primeSubsetGenerator (fun i => Ideal.span {p i}) E *
      secondMaskQuotient p E G hEG :=
  Classical.choose_spec (poisson_mask_generator_dvd p E G hEG)

end

open ActualEisensteinCubic

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeCoreCoefficient cubeOddSupport coreRayCoefficient coreRayTwist
  coreRayCharacter dilatedCoreRow dilatedRayColumn afterDilationLabel b0Label jLabel)
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools
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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

lemma elementNorm_pos (a : O) (ha : a ≠ 0) : 0 < elementNorm a := by
  exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

private theorem active_row_norm_le_one (S T : Finset ι) (a : O) :
    ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
      (fun i => hg i.val) (activeExponent S T) a‖ ≤ 1 := by
  rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
  exact (mul_le_mul (finiteSquarefreeRow_norm_le_one _ hg _ _)
    (finiteSquarefreeRow_norm_le_one _ hg _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem secondPairRadialMode_summable (S T : Finset ι) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => secondPairRadialMode p hp hg hinj S T e k W Y) := by
  let n := ∏ i : activeSupport T S, p i.val
  let G := FiniteGaussPhase.canonicalProductGauss (fun i : activeSupport T S => p i.val)
    (fun i => hp i.val) (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj T S)
    (fun i => hg i.val) (activeExponent T S)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hK : 0 < Y / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) :=
    div_pos hY (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
      (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hn))))
  have hs := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W _ hK
  have hgk (k : O) : ‖activeGaussRowFactor p hp hinj hg T S e k‖ ≤ ‖G‖ := by
    simp only [activeGaussRowFactor, norm_mul, norm_star]
    change ‖G‖ * (_ * _) ≤ ‖G‖
    have hb : ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) e‖ *
        ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) k‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (active_row_norm_le_one p hg T S e)
        (active_row_norm_le_one p hg T S k) (norm_nonneg _) zero_le_one
    exact mul_le_of_le_one_right (norm_nonneg _) hb
  have harg (k : O) : Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) =
      (Y / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) * ‖eisEmbedding k‖ ^ 2 := by ring
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((hs.mul_left ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖).mul_right ‖G‖)
  intro k
  simp only [secondPairRadialMode, norm_mul]
  rw [show (∏ i : activeSupport T S, p i.val) = n from rfl, harg]
  exact mul_le_mul_of_nonneg_left (hgk k) (by positivity)

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem residualSecondMode_eq_frequencyKernel (F G E : Finset ι) (hEG : E ⊆ G)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
    (k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y =
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m (secondMaskQuotient p E G hEG) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k H₁ H₂ W Y := by
  unfold residualSecondMode
  rw [input_pair_fixed_pool p hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂]
  unfold secondFrequencyKernel
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · rw [if_pos hd, if_pos hd]
    have hn : (∏ i : activeSupport T S, p i.val) = ∏ i ∈ S ∪ T, p i := by
      rw [Finset.prod_coe_sort]
      simp only [activeSupport, Finset.sdiff_eq_self_of_disjoint hd,
        Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.union_comm T S]
    simp only [secondPairRadialMode, secondGaussTerm, hn, primeProductNorm,
      ← secondMaskQuotient_spec p E G hEG]
    ring
  · simp [hd]

end SecondPassArithmetic

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
namespace SecondPassArithmetic

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] in
theorem secondInputCoefficient_norm_le (Ψ : O →* ℂ) (m c d : O) (G : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ≤ ‖Ψ (∏ i ∈ G, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) G m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondInputCoefficient, norm_mul, norm_pow,  mul_one]
  calc
    _ ≤ ‖Ψ (∏ i ∈ G, p i)‖ * 1 * 1 ^ 4 * 1 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one _ hg G _
    _ = _ := by ring

end SecondPassArithmetic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalTruncation
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstCauchyArithmetic (activeGaussRowFactor)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem activeGaussRowFactor_norm_le_one
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) (e k : O) :
    ‖activeGaussRowFactor p hp hinj hg S T e k‖ ≤ 1 := by
  have hr (a : O) : ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
      (fun i => hg i.val) (activeExponent S T) a‖ ≤ 1 := by
    rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
    exact (mul_le_mul (finiteSquarefreeRow_norm_le_one _ hg _ _)
      (finiteSquarefreeRow_norm_le_one _ hg _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hGauss := FiniteGaussPhase.norm_canonicalProductGauss
    (fun i : activeSupport S T => p i.val) (fun i => hp i.val)
    (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T)
    (fun i => hg i.val) (fun i => hc i.val) (activeExponent S T)
    (activeExponent_ne_zero S T) (activeExponent_lt_six S T)
  simp only [activeGaussRowFactor, norm_mul, norm_star, hGauss, one_mul]
  exact (mul_le_mul (hr e) (hr k) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc

theorem secondPairRadialMode_summable_norm (S T : Finset ι) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => ‖secondPairRadialMode p hp hg hinj S T e k W Y‖) := by
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hs : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
      (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hn))))
  have hmajor := (EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hs).mul_left
    ‖(Y : ℂ)/(‖eisEmbedding n‖ : ℂ)‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
  intro k
  have ha : Y * ‖eisEmbedding k‖^2 / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2) =
      scale * ‖eisEmbedding k‖^2 := by dsimp [scale]; ring
  simp only [secondPairRadialMode, norm_mul]
  change ‖(Y : ℂ)/(‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
  rw [ha]
  exact mul_le_of_le_one_right (by positivity)
    (activeGaussRowFactor_norm_le_one p hp hg hinj hc T S e k)

end SecondPassArithmetic

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
open FirstPassCubeLabels (columnLog primeProductNorm primeProductNorm_pos)
open ConcreteTraceCRT (eisEmbedding)

theorem mem_secondFrequencyCutoff (scale H : ℝ) (k : O)
    (hk : ‖eisEmbedding k‖^2 ≤ H/scale) : k ∈ secondFrequencyCutoff scale H := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hk
  exact_mod_cast hk.trans (Nat.le_ceil (H/scale))

theorem active_norm_sq_disjoint {ι : Type*} [DecidableEq ι] (p : ι → O)
    (S T : Finset ι) (hd : Disjoint S T) :
    ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 =
      primeProductNorm p S * primeProductNorm p T := by
  rw [Finset.prod_coe_sort]
  simp only [activeSupport, Finset.sdiff_eq_self_of_disjoint hd,
    Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.prod_union hd.symm, map_mul, norm_mul, mul_pow]
  simp only [primeProductNorm]
  ring

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

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem residualSecondMode_tail_eq (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c d : O) (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (K : Finset O) :
    (∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y) =
    ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset, if Disjoint S T then
      residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
        ∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y else 0 := by
  have hs (S T : Finset ι) : Summable (fun k : {k : O // k ∉ K} =>
      if Disjoint S T then residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
        secondPairRadialMode p hp hg hinj S T e k.val W Y else 0) := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd]
      exact ((secondPairRadialMode_summable p hp hg hinj S T e he W Y hY).subtype _).mul_left _
    · simp only [if_neg hd]
      exact summable_zero
  change (∑' k : {k : O // k ∉ K}, ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
    if Disjoint S T then residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
      secondPairRadialMode p hp hg hinj S T e k.val W Y else 0) = _
  rw [Summable.tsum_finsetSum (fun S _ => summable_sum (fun T _ => hs S T))]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Summable.tsum_finsetSum (fun T _ => hs S T)]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, tsum_mul_left]
  · simp [hd]

end

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

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_mono {S T : Finset ι} (hST : S ⊆ T) :
    primeProductNorm p S ≤ primeProductNorm p T := by
  have hd : Disjoint S (T\S) := Finset.disjoint_sdiff
  have hu : S ∪ (T\S) = T := Finset.union_sdiff_of_subset hST
  rw [← hu, FirstPassCubeLabels.primeProductNorm_union p S (T\S) hd]
  exact le_mul_of_one_le_right (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
    (primeProductNorm_ge_one p hp _)

include hinj in
theorem boundedPrimeSupports_card (F : Finset ι) (X : ℝ) (hX : 1 ≤ X) :
    ((boundedPrimeSupports p F X).card : ℝ) ≤ 128*X := by
  let q : Finset ι → Ideal O := fun S => ∏ i ∈ S, Ideal.span {p i}
  have hq : Function.Injective q := FirstCauchyArithmetic.family_product_injective _ hinj
  let I := (boundedPrimeSupports p F X).image q
  have hcard : I.card = (boundedPrimeSupports p F X).card := Finset.card_image_of_injective _ hq
  rw [← hcard]
  apply DescentFiberCost.finite_ideal_count_real I X hX
  · intro J hJ
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))
  · intro J hJ
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
    rw [← primeProductNorm_eq_ideal_norm p S]
    exact (Finset.mem_filter.mp hS).2

end SecondPassArithmetic

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
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
lemma residualPairWeight_test_ne_zero
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι)
    (hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0) :
    H₁ S ≠ 0 ∧ H₂ T ≠ 0 := by
  constructor
  · intro hz
    apply hw
    simp only [residualPairWeight, secondInputCoefficient, hz, mul_zero, star_zero, zero_mul]
  · intro hz
    apply hw
    simp only [residualPairWeight, secondInputCoefficient, hz, mul_zero]

end

end SecondPassArithmetic

open scoped BigOperators Classical

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

include hinj in
theorem sourceSupportMobius_norm (E : Finset ι) :
    ‖supportMobius (fun i => Ideal.span {p i}) E‖ = 1 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have h := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj E)
  simp only [norm_mul, norm_one] at h
  nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) E)]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeSubsetGenerator_norm_eq_productNorm (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 = primeProductNorm p E := by
  rw [primeSubsetGenerator_norm_sq, primeProductNorm_eq_ideal_norm]

include hp hinj in
theorem secondSourceCommonCoefficient_norm_le_one
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (G E : Finset ι) :
    ‖secondSourceCommonCoefficient p hg Ψ m c d G E‖ ≤ 1 := by
  have hA := (secondInputCoefficient_norm_le p hg Ψ m c d G).trans (hΨ _)
  have hA2 : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hN := primeProductNorm_ge_one p hp E
  have hμ := sourceSupportMobius_norm p hinj E
  change ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ)‖ = 1 at hμ
  simp only [secondSourceCommonCoefficient, norm_mul, norm_div,
    Complex.norm_of_nonneg (sq_nonneg _), primeSubsetGenerator_norm_eq_productNorm,
    Complex.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp E).le, hμ]
  exact (mul_le_of_le_one_left (div_nonneg zero_le_one (zero_le_one.trans hN))
    hA2).trans ((div_le_one (by linarith)).mpr hN)

omit [DecidableEq ι] in
theorem secondInputCoefficient_norm_le_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d H S‖ ≤ ‖H S‖ := by
  have he : secondInputCoefficient p hg Ψ m c d H S =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) S * H S := by
    simp only [secondInputCoefficient, mul_one]
  rw [he, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ((secondInputCoefficient_norm_le p hg Ψ m c d S).trans (hΨ _))

end
section

theorem tail_radial_scalar_le (Y E n lengthScale H P : ℝ) (A : ℕ)
    (hY : 0 < Y) (hE : 0 < E) (hn : 1 ≤ n) (hL : 1 ≤ lengthScale)
    (hden : E*n^2 ≤ lengthScale^3) (hH : 0 ≤ H) (hP : 0 ≤ P) :
    (Y/n) * (P / ((min 1 (Y/(E*n^2)))^2 * (1+H)^A)) ≤
      Y*P*(1+lengthScale^3/Y)^2 / (1+H)^A := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have he : 0 < E*n^2 := mul_pos hE (sq_pos_of_pos hn0)
  have hs : 0 < Y/(E*n^2) := div_pos hY he
  have hr : 0 ≤ lengthScale^3/Y := div_nonneg (pow_nonneg (zero_le_one.trans hL) _) hY.le
  have hi : (min 1 (Y/(E*n^2)))⁻¹ ≤ 1+lengthScale^3/Y := by
    by_cases h : 1 ≤ Y/(E*n^2)
    · rw [min_eq_left h, inv_one]
      linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), inv_div]
      exact (div_le_div_of_nonneg_right hden hY.le).trans (by linarith)
  have hi0 : 0 ≤ (min 1 (Y/(E*n^2)))⁻¹ := inv_nonneg.mpr (le_min zero_le_one hs.le)
  have hi2 := pow_le_pow_left₀ hi0 hi 2
  have hyn : Y/n ≤ Y := div_le_self hY.le hn
  calc
    _ = (Y/n)*P*((min 1 (Y/(E*n^2)))⁻¹)^2 / (1+H)^A := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith) _)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hyn hP) hi2 (sq_nonneg _) (mul_nonneg hY.le hP)

theorem sum_pair_indicator {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (U : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, if P a ∧ P b then U else 0) =
      ((s.filter P).card : ℝ)^2 * U := by
  calc
    _ = ∑ a ∈ s.filter P, ∑ b ∈ s.filter P, U := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : P a
      · simp only [h, true_and, ite_true]
      · simp only [h, false_and, ite_false, Finset.sum_const_zero]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, pow_two]; ring

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm)

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.UniformTailBounds
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
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog primeProductNorm)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

theorem full_uniform_secondPairRadialMode_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∑' k : {k : O // H ≤ scale * ‖eisEmbedding k‖^2},
        ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
    S T e he W Y H hY hH
  dsimp only
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hnorm : 0 < ‖eisEmbedding n‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hn)
  have hscale : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he))) (sq_pos_of_pos hnorm))
  let tailSet : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let c := Y / ‖eisEmbedding n‖
  have hc0 : 0 ≤ c := (div_pos hY hnorm).le
  have hpnt (k : tailSet) : ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖ := by
    have ha : Y * ‖eisEmbedding k.val‖^2 / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2) =
        scale * ‖eisEmbedding k.val‖^2 := by dsimp [scale]; ring
    simp only [secondPairRadialMode, norm_mul]
    change ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
    rw [ha, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hY, abs_of_pos hnorm]
    exact mul_le_of_le_one_right (by positivity)
      (activeGaussRowFactor_norm_le_one p hp hg hinj hc T S e k.val)
  have hmajor : Summable (fun k : tailSet =>
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖) :=
    ((EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale).subtype tailSet).mul_left c
  have hsmall : Summable (fun k : tailSet => ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑' k : tailSet, c * ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := hsmall.tsum_le_tsum hpnt hmajor
    _ = c * ∑' k : tailSet, ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound W scale H hscale hH) hc0

theorem full_uniform_secondPairRadialMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H → ∀ K : Finset O,
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∀ k : O, k ∉ K → H ≤ scale * ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
        (Y/‖eisEmbedding n‖) *
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro S T e he W Y H hY hH K
  dsimp only
  intro hK
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  let small : Set O := {k | k ∉ K}
  let large : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let f : small → large := fun k => ⟨k.val,hK k.val k.property⟩
  have hi : Function.Injective f := by
    intro a b heq
    exact Subtype.ext (congrArg (fun z : large => z.val) heq)
  have hs := secondPairRadialMode_summable_norm p hp hg hinj hc S T e he W Y hY
  calc
    _ ≤ ∑' k : small, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      norm_tsum_le_tsum_norm (hs.subtype small)
    _ ≤ ∑' k : large, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH

theorem full_uniform_residualSecondMode_tail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
      (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H → ∀ K : Finset O,
      (∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0 →
        ∀ k : O, k ∉ K →
          H ≤ (Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) *
            ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y‖ ≤
      residualTailCost p hg F G Ψ₁ Ψ₂ m c d H₁ H₂ e Y H A (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y H hY hH K hK
  rw [residualSecondMode_tail_eq p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y hY K]
  unfold residualTailCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, norm_mul]
    by_cases hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T = 0
    · simp only [hw, norm_zero, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hb S T e he W Y H hY hH K (hK S hS T hT hd hw)) (norm_nonneg _)
  · simp [hd]

theorem full_uniform_secondSourceTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ)
      (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
      ∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_residualSecondMode_tail_bound A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F Ψ m c d Hcol W Y H hY hH K hK
  unfold secondSourceTail
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E hE
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))]
  exact hb F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) (primeSubsetGenerator_ne_zero _ _)
    W Y H hY hH (K G E.val) (hK G hG E)

end SecondPassArithmetic

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap

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

lemma outside_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis)
    (hk : k ∉ childFrequencyBall a R) : R < ‖eisEmbedding (a*k)‖^2 :=
  lt_of_not_ge (fun h => hk ((mem_childFrequencyBall a ha R k).mpr h))

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Marks
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem primeSlot_norm_le (L A : Finset ι) (a : ι → ℂ)
    (ha : ∀ p ∈ L, ‖a p‖ ≤ 1) :
    ‖primeSlot L a A‖ ≤ ((L ∩ A).card : ℝ) := by
  simp only [primeSlot, Finset.sum_ite_mem]
  apply (norm_sum_le _ _).trans
  calc
    ∑ p ∈ L ∩ A, ‖a p‖ ≤ ∑ p ∈ L ∩ A, (1 : ℝ) :=
      Finset.sum_le_sum fun p hp => ha p (Finset.mem_inter.mp hp).1
    _ = _ := by simp

omit [DecidableEq σ] in
theorem primeMark_norm_le_divisor_count (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι)
    (hL : (I : Set σ).PairwiseDisjoint L)
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) :
    ‖primeMark I L a A‖ ≤ (2 : ℝ) ^ A.card := by
  have hdis : (I : Set σ).PairwiseDisjoint (fun i => L i ∩ A) := by
    intro i hi j hj hij
    exact (hL hi hj hij).mono (Finset.inter_subset_left) (Finset.inter_subset_left)
  have hcard : (∑ i ∈ I, (L i ∩ A).card) ≤ A.card := by
    rw [← Finset.card_biUnion hdis]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hp).2
  calc
    ‖primeMark I L a A‖ = ∏ i ∈ I, ‖primeSlot (L i) (a i) A‖ := by
      exact norm_prod _ _
    _ ≤ ∏ i ∈ I, ((L i ∩ A).card : ℝ) := by
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
        (fun i hi => primeSlot_norm_le _ _ _ (ha i hi))
    _ ≤ ∏ i ∈ I, (2 : ℝ) ^ (L i ∩ A).card := by
      apply Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
      intro i hi
      exact_mod_cast (Nat.le_of_lt (L i ∩ A).card.lt_two_pow_self)
    _ = (2 : ℝ) ^ (∑ i ∈ I, (L i ∩ A).card) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (2 : ℝ) ^ A.card := pow_le_pow_right₀ (by norm_num) hcard

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.MarkBounds
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

 theorem finite_primeSupport_card {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (U : Finset ι) :
    (IdealMobiusDivisorSum.primeSupport (Ideal.span {∏ i ∈ U, p i})).card = U.card := by
  have hc : Pairwise (Function.onFun IsCoprime (fun i : U => Ideal.span {p i.val})) := by
    intro i j hij
    exact hcop (fun he => hij (Subtype.ext he))
  have he := Fintype.card_congr (productPrimeIndexEquiv (fun i : U => p i.val) hc)
  simpa only [Finset.prod_coe_sort, PrimeIndex, Fintype.card_coe, CompletedGauss.primeSupport, IdealMobiusDivisorSum.primeSupport] using he.symm

theorem finite_primeMark_extracted_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) → ∀ A U : Finset ι,
      ‖primeMark slots lists a (A ∪ U)‖ ≤ (2:ℝ)^A.card * C * (primeProductNorm p U)^ε := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A U
  have hI : (Ideal.span {∏ i ∈ U, p i} : Ideal Eis) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  have hh := hb (Ideal.span {∏ i ∈ U, p i}) hI
  rw [finite_primeSupport_card p hcop U] at hh
  have hn : (Ideal.absNorm (Ideal.span {∏ i ∈ U, p i}) : ℝ) = primeProductNorm p U :=
    (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span _).symm
  rw [hn] at hh
  calc
    _ ≤ (2:ℝ)^(A ∪ U).card := primeMark_norm_le_divisor_count _ _ _ _ hslots ha
    _ ≤ (2:ℝ)^(A.card+U.card) := pow_le_pow_right₀ (by norm_num) (Finset.card_union_le _ _)
    _ = (2:ℝ)^A.card * (2:ℝ)^U.card := pow_add _ _ _
    _ ≤ (2:ℝ)^A.card * (C * (primeProductNorm p U)^ε) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondTailCost
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem residualPairWeight_bounded_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O)
    (Hcol : Finset ι → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (G S T : Finset ι) :
    ‖residualPairWeight p hg Ψ Ψ m c d
      (fun U => Hcol (G ∪ U)) (fun U => Hcol (G ∪ U)) S T‖ ≤ B^2 := by
  simp only [residualPairWeight, norm_mul, norm_star, sourceSupportMobius_norm p hinj, one_mul]
  have hS := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (fun U => Hcol (G ∪ U)) S).trans (hcol _)
  have hT := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (fun U => Hcol (G ∪ U)) T).trans (hcol _)
  simpa only [pow_two] using mul_le_mul hS hT (norm_nonneg _) hB

include hp hinj
theorem residualTailCost_bounded_test
    (F G E : Finset ι) (hEG : E ⊆ G) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (Hcol : Finset ι → ℂ) (B Y H lengthScale P : ℝ) (A : ℕ)
    (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) :
    residualTailCost p hg F G Ψ Ψ m c d
      (fun S => Hcol (G∪S))
      (fun S => Hcol (G∪S))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P ≤
      if primeProductNorm p G ≤ lengthScale then
        (128*lengthScale)^2 * (B^2 *
          (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) else 0 := by
  let C := B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w := residualPairWeight p hg Ψ Ψ m c d
    (fun S => Hcol (G∪S))
    (fun S => Hcol (G∪S))
  have hsupp (S T : Finset ι) (hw : w S T ≠ 0) :
      primeProductNorm p G ≤ lengthScale ∧ primeProductNorm p E ≤ lengthScale ∧
      primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale := by
    obtain ⟨hS,hT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
    have hGS := hsupport (G ∪ S) hS
    have hGT := hsupport (G ∪ T) hT
    have hG := (primeProductNorm_mono p hp Finset.subset_union_left).trans hGS
    exact ⟨hG, (primeProductNorm_mono p hp hEG).trans hG,
      (primeProductNorm_mono p hp Finset.subset_union_right).trans hGS,
      (primeProductNorm_mono p hp Finset.subset_union_right).trans hGT⟩
  by_cases hG : primeProductNorm p G ≤ lengthScale
  · rw [if_pos hG]
    calc
      _ ≤ ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
          if primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale then C else 0 := by
        unfold residualTailCost
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro T hT
        by_cases hd : Disjoint S T
        · rw [if_pos hd]
          dsimp only
          by_cases hw : w S T = 0
          · change ‖w S T‖ * _ ≤ _
            rw [hw, norm_zero, zero_mul]
            split_ifs <;> positivity
          · obtain ⟨_,hE,hSn,hTn⟩ := hsupp S T hw
            rw [if_pos ⟨hSn,hTn⟩]
            have hn2 : ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 =
                primeProductNorm p S * primeProductNorm p T := active_norm_sq_disjoint p S T hd
            have hn : 1 ≤ ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖ := by
              have hpS := primeProductNorm_ge_one p hp S
              have hpT := primeProductNorm_ge_one p hp T
              have hpST : 1 ≤ primeProductNorm p S * primeProductNorm p T := one_le_mul_of_one_le_of_one_le hpS hpT
              rw [← hn2] at hpST
              nlinarith [norm_nonneg (eisEmbedding (∏ i : activeSupport T S, p i.val))]
            have hNe : 0 < ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 :=
              SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)
            have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
                ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 ≤ lengthScale^3 := by
              rw [primeSubsetGenerator_norm_eq_productNorm, hn2]
              have hST := mul_le_mul hSn hTn (FirstPassCubeLabels.primeProductNorm_pos p hp T).le
                (zero_le_one.trans hL)
              have hEST := mul_le_mul hE hST
                (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
                  (FirstPassCubeLabels.primeProductNorm_pos p hp T).le) (zero_le_one.trans hL)
              nlinarith
            have hscalar := tail_radial_scalar_le Y
              (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2)
              (‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖) lengthScale H P A hY hNe hn hL hden hH hP
            exact mul_le_mul (residualPairWeight_bounded_test p hg hinj Ψ hΨ m c d Hcol B hB hcol G S T)
              hscalar (by positivity) (sq_nonneg _)
        · rw [if_neg hd]
          split_ifs <;> positivity
      _ = ((boundedPrimeSupports p (F\G) lengthScale).card : ℝ)^2 * C :=
        sum_pair_indicator (F\G).powerset (fun S => primeProductNorm p S ≤ lengthScale) C
      _ ≤ (128*lengthScale)^2 * C := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (boundedPrimeSupports_card p hinj (F\G) lengthScale hL) 2) hC
  · rw [if_neg hG]
    have hz : residualTailCost p hg F G Ψ Ψ m c d
        (fun S => Hcol (G∪S))
        (fun S => Hcol (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P = 0 := by
      unfold residualTailCost
      apply Finset.sum_eq_zero
      intro S hS
      apply Finset.sum_eq_zero
      intro T hT
      by_cases hd : Disjoint S T
      · rw [if_pos hd]
        have hw : w S T = 0 := by
          by_contra hw
          exact hG (hsupp S T hw).1
        change ‖w S T‖ * _ = 0
        rw [hw, norm_zero, zero_mul]
      · rw [if_neg hd]
    exact hz.le

theorem secondSourceTailCost_bounded_test
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (Hcol : Finset ι → ℂ) (B Y H lengthScale P : ℝ) (A : ℕ)
    (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
      residualTailCost p hg F G Ψ Ψ m c d
        (fun S => Hcol (G∪S))
        (fun S => Hcol (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A P) ≤
      (128*lengthScale)^4 * (B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  let C := B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h128 : 0 ≤ 128*lengthScale := by positivity
  calc
    _ ≤ ∑ G ∈ F.powerset, if primeProductNorm p G ≤ lengthScale then (128*lengthScale)^3*C else 0 := by
      apply Finset.sum_le_sum
      intro G hG
      by_cases hGn : primeProductNorm p G ≤ lengthScale
      · rw [if_pos hGn]
        have heq : boundedPrimeSupports p G lengthScale = G.powerset := by
          apply Finset.filter_eq_self.mpr
          intro E hE
          exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hE)).trans hGn
        have hcard : (G.powerset.card : ℝ) ≤ 128*lengthScale := by
          simpa only [heq] using boundedPrimeSupports_card p hinj G lengthScale hL
        calc
          _ ≤ ∑ E : G.powerset, (128*lengthScale)^2*C := by
            apply Finset.sum_le_sum
            intro E hE
            have hr := residualTailCost_bounded_test p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
              Ψ hΨ m c d Hcol B Y H lengthScale P A hB hY hH hP hL hcol hsupport
            rw [if_pos hGn] at hr
            have hc := secondSourceCommonCoefficient_norm_le_one p hp hg hinj Ψ hΨ m c d G E.val
            exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans
              (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hC))
          _ = (G.powerset.card : ℝ)*((128*lengthScale)^2*C) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          _ ≤ (128*lengthScale)*((128*lengthScale)^2*C) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hC)
          _ = _ := by ring
      · rw [if_neg hGn]
        apply Finset.sum_nonpos
        intro E hE
        have hr := residualTailCost_bounded_test p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
          Ψ hΨ m c d Hcol B Y H lengthScale P A hB hY hH hP hL hcol hsupport
        rw [if_neg hGn] at hr
        exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hr
    _ = ((boundedPrimeSupports p F lengthScale).card : ℝ)*((128*lengthScale)^3*C) := by
      rw [← Finset.sum_filter]
      simp only [boundedPrimeSupports, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128*lengthScale)*((128*lengthScale)^3*C) :=
      mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F lengthScale hL)
        (mul_nonneg (pow_nonneg h128 _) hC)
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondWholeTail
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_second_supported_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H lengthScale : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ lengthScale →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
        (128*lengthScale)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+lengthScale^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_secondSourceTail_bound order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Hcol W B Y H lengthScale hB hY hH hL hcol hsupp K hK
  exact (htail p hp hg hinj hc F Ψ m c d Hcol W Y H hY hH K hK).trans
    (secondSourceTailCost_bounded_test p hp hg hinj F Ψ hΨ m c d Hcol B Y H lengthScale
      (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) order hB hY hH (by positivity) hL hcol hsupp)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondWholeCutoff
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_whole_column_denominator {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal] (G E S T : Finset ι)
    (hEG : E ⊆ G) (hGS : Disjoint G S) (hGT : Disjoint G T)
    (L : ℝ) (hL : 0 ≤ L)
    (hS : primeProductNorm p (G ∪ S) ≤ L)
    (hT : primeProductNorm p (G ∪ T) ≤ L) :
    (primeProductNorm p E)^2 * (primeProductNorm p S * primeProductNorm p T) ≤ L^2 := by
  have hE := primeProductNorm_mono p hp hEG
  have hE0 := (primeProductNorm_pos p hp E).le
  have hS0 := (primeProductNorm_pos p hp S).le
  have hT0 := (primeProductNorm_pos p hp T).le
  rw [primeProductNorm_union p G S hGS] at hS
  rw [primeProductNorm_union p G T hGT] at hT
  calc
    _ ≤ (primeProductNorm p G)^2 * (primeProductNorm p S * primeProductNorm p T) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hE0 hE 2) (mul_nonneg hS0 hT0)
    _ = (primeProductNorm p G * primeProductNorm p S) *
      (primeProductNorm p G * primeProductNorm p T) := by ring
    _ ≤ L*L := mul_le_mul hS hT (mul_nonneg (primeProductNorm_pos p hp G).le hT0) hL
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCorrelatedCutoff
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_correlated_column_denominator {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (G E S T : Finset ι) (hGS : Disjoint G S) (hGT : Disjoint G T)
    (L : ℝ) (hL : 0 ≤ L)
    (hS : primeProductNorm p (G ∪ S) ≤ L)
    (hT : primeProductNorm p (G ∪ T) ≤ L) :
    (primeProductNorm p E)^2 * (primeProductNorm p S * primeProductNorm p T) ≤
      (primeProductNorm p E/primeProductNorm p G)^2 * L^2 := by
  have hG0 := (primeProductNorm_pos p hp G).ne'
  have hbound := second_whole_column_denominator p hp G G S T Finset.Subset.rfl hGS hGT L hL hS hT
  calc
    _ = (primeProductNorm p E/primeProductNorm p G)^2 *
      ((primeProductNorm p G)^2 * (primeProductNorm p S*primeProductNorm p T)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)

theorem full_second_correlated_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H L : ℝ) (R : Finset ι → Finset ι → ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ L →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ L) →
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        correlatedSecondRadius p d G E.val L Y H ≤ R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun G E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) (R G E))‖ ≤
        (128*L)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+L^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H L R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H L hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hdGS : Disjoint G S := Finset.disjoint_left.mpr (by
    intro i hiG hiS
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hiS)).2 hiG)
  have hdGT : Disjoint G T := Finset.disjoint_left.mpr (by
    intro i hiG hiT
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hT) hiT)).2 hiG)
  have hden := second_correlated_column_denominator p hp G E.val S T hdGS hdGT L (zero_le_one.trans hL)
    (hsupp _ hGS) (hsupp _ hGT)
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have heN : 0 < ‖eisEmbedding e‖^2 := SecondPassIntegration.elementNorm_pos e he
  have henorm : ‖eisEmbedding e‖^2 = primeProductNorm p E.val :=
    primeSubsetGenerator_norm_eq_productNorm p E.val
  have hkR := (outside_childFrequencyBall (d*e) hde (R G E.val) k hk).le
  have hR' : ‖eisEmbedding d‖^2 * (primeProductNorm p E.val/primeProductNorm p G)^2 * L^2 * H ≤
      Y * (‖eisEmbedding d‖^2 * ‖eisEmbedding e‖^2 * ‖eisEmbedding k‖^2) := by
    have hh := (div_le_iff₀ hY).mp (hR G hG E)
    have hh' := mul_le_mul_of_nonneg_right hkR hY.le
    simp only [map_mul,norm_mul,mul_pow] at hh'
    nlinarith
  have hbound : H * (‖eisEmbedding e‖^2 *
      (primeProductNorm p S * primeProductNorm p T)) ≤ Y*‖eisEmbedding k‖^2 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hdN heN)).mp
    have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg hdN.le hH)
    rw [←henorm] at hh
    rw [←henorm] at hR'
    nlinarith [hh,hR']
  rw [active_norm_sq_disjoint p S T hST,div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos heN (mul_pos (primeProductNorm_pos p hp S)
    (primeProductNorm_pos p hp T)))).mpr
  exact hbound

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.PrincipalEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InversePrincipalEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open SecondPassArithmetic FirstPassCubeLabels IdealMobiusDivisorSum
open InverseMoment
local notation "Eis" => ActualEisensteinCubic.O

section
variable {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma markedRadial_support {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (V : 𝓢(ℝ, ℂ)) (X M : ℝ) (hX : 0 < X)
    (hV : ∀ t, V t ≠ 0 → t ≤ Real.exp M) (G : Finset ι)
    (hG : markedRadial p slots lists a A V X G ≠ 0) :
    primeProductNorm p G ≤ X * Real.exp M := by
  have hv : V (primeProductNorm p G / X) ≠ 0 := by
    intro hz
    exact hG (by simp [markedRadial, hz])
  simpa only [mul_comm] using (div_le_iff₀ hX).mp (hV _ hv)

end

end SevenEighths.InversePrincipalEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseSecondPrincipalCaller
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight
open InverseMoment InversePrincipalEnergy RayFourExpansion
local notation "Eis" => ActualEisensteinCubic.O

theorem principalWindow_apply (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    principalWindow om a b ha hs negative t x =
      if negative then normTwistedSource (fun y => star (om y)) (-t) x
      else normTwistedSource om t x := by
  cases negative <;> simp only [principalWindow,Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,
    star_mul,logPhase_conjugate,mul_comm]

theorem principalWindow_norm (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    ‖principalWindow om a b ha hs negative t x‖=‖om x‖ := by
  rw [principalWindow_apply]
  cases negative <;> simp [normTwistedSource,logPhase_norm]

theorem principalWindow_support (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    Function.support (principalWindow om a b ha hs negative t) = Function.support om := by
  ext x
  change (_≠0) ↔ (_≠0)
  rw [←norm_ne_zero_iff,principalWindow_norm,norm_ne_zero_iff]

theorem principalWindow_seminorm_zero (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    SchwartzMap.seminorm ℝ 0 0 (principalWindow om a b ha hs negative t)=
      SchwartzMap.seminorm ℝ 0 0 om := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ om x
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ (principalWindow om a b ha hs negative t) x

theorem principalWindow_upper (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (M : ℝ) (hb : b≤Real.exp M)
    (negative : Bool) (t x : ℝ) (hx : principalWindow om a b ha hs negative t x≠0) :
    x≤Real.exp M := by
  have hmem : x∈Function.support om := by
    rw [←principalWindow_support om a b ha hs negative t]
    exact hx
  exact (hs hmem).2.trans hb

end SevenEighths.InverseSecondPrincipalCaller

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondMarkedTail
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InversePrincipalEnergy InverseSecondPrincipalCaller
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem marked_radial_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → O) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A : Finset ι) (V : 𝓢(ℝ,ℂ)) (X M : ℝ), 0 < X →
      (∀ u, V u ≠ 0 → u ≤ Real.exp M) →
      ∀ U, ‖markedRadial p slots lists a A V X U‖ ≤
        (2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * SchwartzMap.seminorm ℝ 0 0 V := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_extracted_bound ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A V X M hX hV U
  by_cases hz : V (primeProductNorm p U/X) = 0
  · simp only [markedRadial,hz,mul_zero,norm_zero]
    positivity
  · have hn : primeProductNorm p U ≤ X*Real.exp M := by
      simpa only [mul_comm] using (div_le_iff₀ hX).mp (hV _ hz)
    have hn0 : 0 ≤ primeProductNorm p U := (primeProductNorm_pos p hp U).le
    rw [markedRadial,norm_mul]
    apply (mul_le_mul (hmark p hp hcop slots lists a hslots ha A U)
      (V.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)).trans
    gcongr

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondTailAbsorption
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section

lemma second_tail_fixed_cap (Y L cap B P H : ℝ) (order : ℕ)
    (hY : 0<Y) (hL : 0≤L) (hc : 1≤ cap) (_hB : 0≤B) (hP : 0≤P) (hH : 0≤H)
    (hy : Y≤ cap) (hyi : Y⁻¹≤ cap) (hl : L≤ cap) :
    (128*L)^4*(B^2*(Y*P*(1+L^3/Y)^2/(1+H)^order))≤
      (4*128^4)*B^2*P*cap^13/(1+H)^order := by
  have hc0 : 0≤ cap := zero_le_one.trans hc
  have hscale : 1+L^3/Y≤2*cap^4 := by
    calc
      _ ≤ 1+cap^3*cap := by rw [div_eq_mul_inv]; gcongr
      _ ≤ _ := by have hh : 1≤ cap^4 := one_le_pow₀ hc; nlinarith
  calc
    _ = (128*L)^4*B^2*Y*P*(1+L^3/Y)^2/(1+H)^order := by ring
    _ ≤ (128*cap)^4*B^2*cap*P*(2*cap^4)^2/(1+H)^order := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      gcongr
    _ = _ := by ring

theorem choose_second_tail_order (Lcap tau saving : ℝ) (hL : 0≤Lcap) (htau : 0<tau) :
    ∃ order : ℕ,∀ Z Y L B P : ℝ,1≤Z → 0<Y → 0≤L → 0≤B → 0≤P →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → L≤Z^Lcap →
      (128*L)^4*(B^2*(Y*P*(1+L^3/Y)^2/(1+Z^tau)^order))≤
        (4*128^4)*B^2*P*Z^(-saving) := by
  obtain ⟨order,ho⟩ := exists_nat_gt ((13*Lcap+saving)/tau)
  refine ⟨order,?_⟩
  intro Z Y L B P hZ hY hL0 hB hP hy hyi hl
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := second_tail_fixed_cap Y L (Z^Lcap) B P (Z^tau) order hY hL0
    (Real.one_le_rpow hZ hL) hB hP (Real.rpow_pos_of_pos hz _).le hy hyi hl
  have hdecay : (Z^Lcap)^13/(1+Z^tau)^order≤Z^(-saving) := by
    calc
      _ ≤ (Z^Lcap)^13/(Z^tau)^order := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) order)
      _ = Z^(13*Lcap-tau*(order:ℝ)) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        have hh := (div_lt_iff₀ htau).mp ho
        nlinarith
  apply hb.trans
  calc
    _ = ((4*128^4)*B^2*P)*((Z^Lcap)^13/(1+Z^tau)^order) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondRapidTail
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_second_rapid_correlated_tail (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ), (∀ a,‖Ψ a‖≤1) →
      ∀ (m c d : O),d≠0 → ∀ (Hcol : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (Z B Y L : ℝ) (R : Finset ι→Finset ι→ℝ),
      1≤Z → 0≤B → 0<Y → 1≤L → Y≤Z^Lcap → Y⁻¹≤Z^Lcap → L≤Z^Lcap →
      (∀ U,‖Hcol U‖≤B) → (∀ U,Hcol U≠0 → primeProductNorm p U≤L) →
      (∀ G∈F.powerset,∀ E : G.powerset,correlatedSecondRadius p d G E.val L Y (Z^tau)≤R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))‖≤
      C*B^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  obtain ⟨order,horder⟩ := choose_second_tail_order Lcap tau saving hLcap htau
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_correlated_tail order
  refine ⟨s,(4*128^4)*Ct,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W Z B Y L R hZ hB hY hL hy hyi hl hcol hsupp hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have he := htail p hp hg hinj hc F Ψ hΨ m c d hd Hcol W B Y (Z^tau) L R
    hB hY (Real.rpow_pos_of_pos hz _).le hL hcol hsupp hR
  apply he.trans
  have hh := horder Z Y L B (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    hZ hY (zero_le_one.trans hL) hB (mul_nonneg hCt.le (apply_nonneg _ _)) hy hyi hl
  convert (preTransparency := .instances) hh using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.WholePriorityRapidTail
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRapidTail
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseMoment InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O

theorem marked_rapid_tail (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ), (∀u,‖Ψ u‖≤1) →
      ∀ (m c d : O),d≠0 → ∀ (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      ∀ (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (negative : Bool) (height X M Y Z : ℝ)
      (R : Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀G∈F.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (markedRadial p slots lists a ∅ (principalWindow om lo hi hlo hs negative height) X) W Y
        (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))‖≤
      Ct*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_rapid_correlated_tail Lcap tau (saving+Lcap) hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound (1/2) (by norm_num)
  refine ⟨s,Ct*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F Ψ hΨ m c d hd slots lists a hslots ha
    om W lo hi hlo hs negative height X M Y Z R hX hhi hZ hY hL hy hyi hl hR
  let L:=X*Real.exp M
  have hLpos : 0<L := mul_pos hX (Real.exp_pos _)
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hv := principalWindow_upper om lo hi hlo hs M hhi negative height
  have hm := hmark p hp hcop slots lists a hslots ha ∅
    (principalWindow om lo hi hlo hs negative height) X M hX hv
  simp only [Finset.card_empty,pow_zero,one_mul,principalWindow_seminorm_zero] at hm
  have ht := htail p hp hg hinj hc F Ψ hΨ m c d hd _ W Z
    (Cm*L^(1/2:ℝ)*SchwartzMap.seminorm ℝ 0 0 om) Y L R hZ (by positivity) hY hL hy hyi hl hm
    (markedRadial_support p slots lists a ∅ _ X M hX hv) hR
  have hp : (L^(1/2:ℝ))^2=L := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLpos.le]
    norm_num
  have habsorb : L*Z^(-(saving+Lcap))≤Z^(-saving) := by
    calc
      _≤Z^Lcap*Z^(-(saving+Lcap)) := mul_le_mul_of_nonneg_right hl (by positivity)
      _=Z^(-saving) := by rw [←Real.rpow_add hz];congr 1;ring
  apply ht.trans
  calc
    _=(Ct*Cm^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        (L*Z^(-(saving+Lcap))) := by rw [mul_pow,mul_pow,hp];ring
    _≤_ := by
      exact mul_le_mul_of_nonneg_left habsorb (by positivity)

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseWholePriorityRapidTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.WholePriorityParentBounds
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy InversePrioritySecondSource
local notation "O"=>ActualEisensteinCubic.O

variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq σ] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem parent_residual_lists_subset {Jo:ℕ} (extra:CubeCoordinates ι→Finset ι)
    (negative:Bool) (lists:σ→Finset ι) (y:SecondParentSource ι Jo) (i:σ):
    residualLists p negative (fun i=>lists i\extra y.cube) y i⊆lists i:=
by
  intro k hk
  exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hk).1).1

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem parent_residual_lists_pairwise {Jo:ℕ} (extra:CubeCoordinates ι→Finset ι)
    (negative:Bool) (slots assigned:Finset σ) (lists:σ→Finset ι) (y:SecondParentSource ι Jo)
    (hslots:(slots:Set σ).PairwiseDisjoint lists):
    ((slots\assigned:Finset σ):Set σ).PairwiseDisjoint (residualLists p negative (fun i=>lists i\extra y.cube) y):=by
  intro i hi j hj hij
  exact (hslots (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij).mono
    (parent_residual_lists_subset p extra negative lists y i)
    (parent_residual_lists_subset p extra negative lists y j)

theorem priority_tail_parent_uniform_oai (Lcap tau saving:ℝ)(hLcap:0≤Lcap)(htau:0<tau):
    ∃(s:Finset (ℕ×ℕ))(C:ℝ),0<C ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) →
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y Z t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
    ∀{Jo:ℕ}(y:SecondParentSource ι Jo),
      (∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p y) G E.val (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ m slots assigned lists a
        (principalWindow om lo hi hlo hs negative t) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving):=by
  obtain ⟨s,C,hC,hbound⟩:=InverseWholePriorityRapidTail.marked_rapid_tail Lcap tau saving hLcap htau
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc extra pool negative Ψ m slots assigned lists a hslots ha hΨ
    om lo hi hlo hs X M Y Z t R hX hhi hZ hY hscale hy hyi hx Jo y hR
  have hpair:=parent_residual_lists_pairwise p extra negative slots assigned lists y hslots
  have hcoeff:∀i∈slots\assigned,∀k∈residualLists p negative (fun i=>lists i\extra y.cube) y i,‖a i k‖≤1:=by
    intro i hi k hk
    exact ha i (Finset.mem_sdiff.mp hi).1 k (parent_residual_lists_subset p extra negative lists y i hk)
  exact hbound p hp hcop hg hinj hc pool Ψ hΨ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (primeSubsetGenerator_ne_zero _ _)
    (slots\assigned) _ a hpair hcoeff om rowMajorant lo hi hlo hs negative t X M Y Z R
    hX hhi hZ hY hscale hy hyi hx hR

end SevenEighths.InverseMoment

end

end OAI
end

theorem solution.{u_3, u_4} : type_of% @OAI.SevenEighths.InverseMoment.priority_tail_parent_uniform_oai.{u_3, u_4} := @OAI.SevenEighths.InverseMoment.priority_tail_parent_uniform_oai.{u_3, u_4}
