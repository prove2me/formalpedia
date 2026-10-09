-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.original_marked_binned_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:53:19.691836+00:00
-- url     : https://prove2.me/submissions/5266774b-9d48-416d-871d-4b7e36c8eea6

import Mathlib
import Definitions.Def_OAIHecke78B009

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

open ActualEisensteinCubic

open ActualEisensteinCubic

theorem norm_at_least_one (I : Ideal O) (hI : I ≠ 0) :
    (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem triple_scale_bounds (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    a ≤ a * b ^ 3 * c ^ 3 ∧ b ≤ a * b ^ 3 * c ^ 3 ∧ c ≤ a * b ^ 3 * c ^ 3 := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
  have hc3 : 1 ≤ c ^ 3 := one_le_pow₀ hc
  constructor
  · calc a = a * 1 * 1 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr
  constructor
  · calc b ≤ b ^ 3 := le_self_pow₀ hb (by decide)
         _ = 1 * b ^ 3 * 1 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr
  · calc c ≤ c ^ 3 := le_self_pow₀ hc (by decide)
         _ = 1 * 1 * c ^ 3 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr

theorem finite_support_norm_triple (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (F : Ideal O × Ideal O × Ideal O → ℂ)
    (hzero : ∀ I J H, I = 0 ∨ J = 0 ∨ H = 0 → F (I, J, H) = 0)
    (hwindow : ∀ I J H,
      W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
        (Ideal.absNorm H : ℝ) ^ 3 / X) = 0 → F (I, J, H) = 0) :
    (Function.support F).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * X)
  let S := {I : Ideal O | Ideal.absNorm I ≤ M}
  have hS : S.Finite := Ideal.finite_setOfPred_absNorm_le M
  apply (hS.prod (hS.prod hS)).subset
  rintro ⟨I, J, H⟩ hF
  have hF0 : F (I, J, H) ≠ 0 := hF
  have hI : I ≠ 0 := fun h => hF0 (hzero I J H (Or.inl h))
  have hJ : J ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inl h)))
  have hH : H ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inr h)))
  have hw : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
      (Ideal.absNorm H : ℝ) ^ 3 / X) ≠ 0 := fun h => hF0 (hwindow I J H h)
  have hsize := (div_le_iff₀ hX).mp (hbound _ hw)
  have hb := triple_scale_bounds _ _ _ (norm_at_least_one I hI)
    (norm_at_least_one J hJ) (norm_at_least_one H hH)
  have hIM : Ideal.absNorm I ≤ M := by exact_mod_cast (hb.1.trans hsize).trans hM.le
  have hJM : Ideal.absNorm J ≤ M := by exact_mod_cast (hb.2.1.trans hsize).trans hM.le
  have hHM : Ideal.absNorm H ≤ M := by exact_mod_cast (hb.2.2.trans hsize).trans hM.le
  exact ⟨hIM, hJM, hHM⟩

end
section

open ActualEisensteinCubic ConcreteTraceCRT

theorem squarefreeGaussCoefficient_eq (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    squarefreeGaussCoefficient I =
      star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I hI := by
  rw [squarefreeGaussCoefficient, dif_pos ⟨hs, hI⟩]

theorem summand_zero_left (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (J : Ideal O) :
    summand Ψ W X 0 J = 0 := by simp [summand]

theorem summand_zero_right (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I : Ideal O) :
    summand Ψ W X I 0 = 0 := by simp [summand]

theorem summand_zero_window (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O)
    (h : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X) = 0) :
    summand Ψ W X I J = 0 := by simp [summand, Vstar, h]

theorem columnWeight_zero_of_mask (Ψ : O →* ℂ) (I : Ideal O)
    (h : Ψ (primaryGenerator I) = 0) : columnWeight Ψ I = 0 := by
  simp only [columnWeight, h, mul_zero]

theorem cubeWeight_zero_of_mask (Ψ : O →* ℂ) (I : Ideal O)
    (h : Ψ (primaryGenerator I) = 0) : cubeWeight Ψ I = 0 := by
  change _ * Ψ (primaryGenerator I) ^ 3 / _ = 0
  rw [h, zero_pow (by decide), mul_zero, zero_div]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

theorem ideal_cube_convolution (c : Ideal O →* ℂ) (hc0 : c 0 = 0)
    (f : Ideal O → ℂ)
    (hfinite : (Function.support (fun p : Ideal O × Ideal O =>
      (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2))).Finite) :
    (∑' H : Ideal O, ∑' J : Ideal O,
      (UniqueFactorizationMonoid.moebius H : ℂ) * c (H * J) * f (H * J)) = f 1 := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    (UniqueFactorizationMonoid.moebius p.1 : ℂ) * c (p.1 * p.2) * f (p.1 * p.2)
  have hF : Summable F := summable_of_hasFiniteSupport hfinite
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.val) =
      if B = 1 then f 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have heach : ∀ p : MulFiber 0, F p.val = 0 := by
        intro p
        dsimp [F]
        rw [p.property, hc0, mul_zero, zero_mul]
      simp only [heach, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = ∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) * (c B * f B) := by
          apply tsum_congr
          intro p
          dsimp [F]
          rw [p.property, mul_assoc]
        _ = (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) * (c B * f B) := by
          rw [tsum_mul_right]
        _ = if B = 1 then f 1 else 0 := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with h
          · subst B; simp only [map_one, one_mul]
          · simp
  have hs := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.val) (∑' p, F p) at hs
  simp_rw [hfiber] at hs
  have hsum : (∑' p, F p) = f 1 := by
    have he := hs.tsum_eq.symm
    simpa only [tsum_ite_eq, one_ne_zero] using he
  rw [← hF.tsum_prod]
  exact hsum

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

theorem finite_support_expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O × Ideal O =>
      expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite := by
  apply finite_support_norm_triple W hW X hX
  · intro I H J hz
    rcases hz with rfl | rfl | rfl <;> simp [expandedTerm]
  · intro I H J hw
    simp [expandedTerm, Vstar, hw]

theorem expandedTerm_scale (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J = expandedTerm Ψ W X I H J := by
  have harg : (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 /
      (X / (Ideal.absNorm H : ℝ) ^ 3) =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X := by
    rw [div_div_eq_mul_div]
    ring
  simp only [summand, expandedTerm, harg, map_mul]
  ring

theorem expandedTerm_one (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) :
    expandedTerm Ψ W X I 1 J = summand Ψ W X I J := by
  simp only [expandedTerm, summand, UniqueFactorizationMonoid.moebius_one, Int.cast_one,
    one_mul, map_one, Nat.cast_one, one_pow, mul_one]
  ring

theorem completedT_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2)).Finite := by
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hinj : Function.Injective (fun p : Ideal O × Ideal O => (p.1, (1 : Ideal O), p.2)) := by
    intro a b hab
    exact Prod.ext (Prod.mk.inj hab).1 (Prod.mk.inj (Prod.mk.inj hab).2).2
  have hp := Set.Finite.preimage hinj.injOn hf
  change (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X p.1 1 p.2)).Finite at hp
  simpa only [expandedTerm_one] using hp

theorem vstar_source_normalization (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (hX : 0 < X) (I : Ideal O) :
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X) =
      (Real.sqrt X : ℂ)⁻¹ * columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X) := by
  by_cases hI : I = 0
  · subst I; simp
  have hN : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)
  have hsN : (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hN).ne'
  have hsX : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hX).ne'
  rw [Vstar, Real.sqrt_div hN.le, Complex.ofReal_div]
  field_simp

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

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

theorem mask_mul (a b : O) :
    rowCoprimeMask P S (a * b) = rowCoprimeMask P S a * rowCoprimeMask P S b := by
  simp only [← row_sixth P hg S, finiteSquarefreeRow_mul, mul_pow]

end Rows

end FirstPassCubeLabels

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

lemma normLogBin_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    normLogBin u ≤ normLogBin v := Nat.floor_mono (Real.log_le_log hu huv)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.GlobalEncoding
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

section
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
include hinj

theorem primeIdealProduct_emultiplicity (S : Finset ι) (v : ι → ℕ) (i : ι) :
    emultiplicity (P i) (∏ j ∈ S, P j ^ v j) = if i ∈ S then (v i : ℕ∞) else 0 := by
  have hp (j : ι) : Prime (P j) := Ideal.prime_of_isPrime (NeZero.ne (P j)) inferInstance
  rw [Finset.emultiplicity_prod (hp i)]
  have hz (j : ι) (hji : j ≠ i) : emultiplicity (P i) (P j ^ v j) = 0 := by
    rw [emultiplicity_pow (hp i), emultiplicity_eq_zero_of_irreducible_ne
      (hp i).irreducible (hp j).irreducible (fun he => hji (hinj he).symm), mul_zero]
  by_cases hi : i ∈ S
  · rw [if_pos hi,Finset.sum_eq_single i]
    · exact emultiplicity_pow_self_of_prime (hp i) (v i)
    · intro j hj hji
      exact hz j hji
    · exact fun hn => (hn hi).elim
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (fun he => hi (he ▸ hj))

end

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FundamentalDomain
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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O

attribute [fun_prop] hyperbolicGram_continuous hyperbolicFrobenius_continuous

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

theorem large_cube_convolution (H₀ : ℝ) (c : Ideal O →* ℂ) (hc0 : c 0=0)
    (f : Ideal O → ℂ)
    (hfinite : (Function.support (fun p : Ideal O × Ideal O =>
      (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2))).Finite) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then
        (UniqueFactorizationMonoid.moebius H : ℂ)*c (H*J)*f (H*J) else 0) =
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*c B*f B := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.1 : ℝ) then
      (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2) else 0
  have hF : Summable F := summable_of_hasFiniteSupport (hfinite.subset (by
    intro p hp
    by_contra hn
    have he : (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2)=0 := not_ne_iff.mp hn
    exact hp (by dsimp [F];rw [he];simp)))
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.val)=largeCubeCoefficient H₀ B*c B*f B := by
    by_cases hB : B=0
    · subst B
      have hz : ∀ p : MulFiber 0,F p.val=0 := by
        intro p
        dsimp [F]
        rw [p.property,hc0]
        simp
      simp [hz,largeCubeCoefficient]
    · let e := mulFiberDivisorEquiv B hB
      have hsum : (∑' p : MulFiber B,
          if H₀ ≤ (Ideal.absNorm p.val.1 : ℝ) then (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) else 0) =
          largeCubeCoefficient H₀ B := by
        calc
          _ = ∑' H : {H : Ideal O // H∈idealDivisors B},
              if H₀ ≤ (Ideal.absNorm H.val : ℝ) then (UniqueFactorizationMonoid.moebius H.val : ℂ) else 0 :=
            e.tsum_eq _
          _ = _ := by
            rw [tsum_fintype,largeCubeCoefficient,if_neg (show B≠⊥ from hB)]
            exact (Finset.sum_subtype (idealDivisors B) (fun H => Iff.rfl)
              (fun H => if H₀ ≤ (Ideal.absNorm H : ℝ) then (UniqueFactorizationMonoid.moebius H : ℂ) else 0)).symm
      calc
        _ = ∑' p : MulFiber B,
            (if H₀ ≤ (Ideal.absNorm p.val.1 : ℝ) then (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) else 0)*(c B*f B) := by
          apply tsum_congr
          intro p
          dsimp [F]
          rw [p.property]
          split_ifs <;> ring
        _ = _ := by rw [tsum_mul_right,hsum];ring
  have hs := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.val) (∑' p,F p) at hs
  simp_rw [hfiber] at hs
  rw [← hF.tsum_prod]
  exact hs.tsum_eq.symm

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer
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
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge

theorem sum_selected_ideals (F : Finset (Ideal O)) (hF : ∀I∈F,Squarefree I)
    (a : Ideal O→ℂ) :
    (∑I∈F,a I)=∑S∈(Finset.univ:Finset (primePool F)).powerset,
      if (∏i∈S,i.val)∈F then a (∏i∈S,i.val) else 0 := by
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun S _ => ∏i∈S,i.val)
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · intro S hS T hT he
    exact family_product_injective (fun i:primePool F => i.val) Subtype.val_injective he
  · intro I hI
    refine ⟨idealSupport F I,?_,idealSupport_product_eq F hI (hF I hI)⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),?_⟩
    rwa [idealSupport_product_eq F hI (hF I hI)]
  · intro S hS
    rfl

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.InputEnergy
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
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm columnLog)

theorem poolProduct_admissible (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (S : Finset (primePool F)) : Admissible (∏ i ∈ S,i.val) := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏ i ∈ S,i.val) ≠ (0 : Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  refine ⟨hn, ?_, ?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))).isRelPrime
    · intro i hi
      exact (hp i).squarefree
  · intro P hP
    obtain ⟨hprime, hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
    obtain ⟨i, hi, hPi⟩ := (hprime.dvd_finsetProd_iff (fun i : primePool F => i.val)).mp hdiv
    have he : P=i.val := (prime_dvd_prime_iff_eq hprime (hp i)).mp hPi
    rw [he]
    exact ⟨poolGood F hF i, poolOdd F hF i⟩

theorem poolPrimary_norm (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (S : Finset (primePool F)) :
    primeProductNorm (poolPrimary F) S = (Ideal.absNorm (∏ i ∈ S,i.val) : ℝ) := by
  rw [primeProductNorm, eisEmbedding_norm_sq_eq_absNorm_span, FiniteGaussPhase.span_finset_prod]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact poolPrimary_span F hF i

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.OutsideIdeals
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
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm columnLog)

theorem outside_pool_product_not_dvd (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀ P ∈ S, Prime P) (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    ∀ P ∈ S, ¬ P ∣ ∏ i ∈ T,i.val := by
  intro P hPS hdiv
  obtain ⟨i,hi,hPi⟩ := ((hSp P hPS).dvd_finsetProd_iff
    (fun i : primePool (outsideSquarefreeIdeals S D) => i.val)).mp hdiv
  obtain ⟨I,hIF,hiI⟩ := mem_primePool_iff.mp i.property
  have ho : I ∈ outsideIdealsUpTo S D := (Finset.mem_filter.mp hIF).1
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  have hd : i.val ∣ I := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hiI |>.2
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P hPS (hPi.trans hd)

theorem selectedIdealTest_outside (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (b Z : ℝ) (hZ : 0 < Z)
    (hs : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*Z ≤ D)
    (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    selectedIdealTest (outsideSquarefreeIdeals S D) (fun n => W (n/Z)) T =
    W (primeProductNorm (poolPrimary (outsideSquarefreeIdeals S D)) T/Z) := by
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  rw [poolPrimary_norm F hF T]
  unfold selectedIdealTest
  by_cases hw : W ((Ideal.absNorm (∏ i ∈ T,i.val) : ℝ)/Z)=0
  · split_ifs
    · rfl
    · exact hw.symm
  · rw [if_pos]
    have ha := poolProduct_admissible F hF T
    apply Finset.mem_filter.mpr
    refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,outside_pool_product_not_dvd S D hSp T⟩,ha.2.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr (fun hz => ha.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact_mod_cast ((div_le_iff₀ hZ).mp (hs _ hw)).trans hD

end InitialMeanSquare

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.HighRadialBounds
namespace OAI

noncomputable section

namespace InitialMeanSquare

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

section

open scoped BigOperators Classical

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem outside_prime_divisor_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I Q : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) (hQ : Prime Q)
    (hd : Q ∣ I) : Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  have hQpos : 1 ≤ Ideal.absNorm Q := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hQ.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  have hQI : Ideal.absNorm Q ≤ Ideal.absNorm I :=
    Nat.le_of_dvd (mem_outsideIdealsUpTo.mp hI).1 (map_dvd Ideal.absNorm hd)
  have hQo : Q ∈ outsideIdealsUpTo S D := mem_outsideIdealsUpTo.mpr
    ⟨hQpos, hQI.trans (mem_outsideIdealsUpTo.mp hI).2.1,
      fun P hP hPQ => (mem_outsideIdealsUpTo.mp hI).2.2 P hP (hPQ.trans hd)⟩
  apply mem_primePool_iff.mpr
  refine ⟨Q, Finset.mem_filter.mpr ⟨hQo,hQ.squarefree⟩,?_⟩
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.ne_zero).mpr
    ⟨hQ,dvd_rfl⟩

theorem outside_factors_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) :
    ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  intro Q hQ
  obtain ⟨hprime,hdiv⟩ :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (outsideIdealsUpTo_ne_bot S D I hI)).mp hQ
  exact outside_prime_divisor_mem_pool S D hI hprime hdiv

end

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm )

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end InitialMeanSquare

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

theorem columnWeight_zero_of_not_squarefree (Ψ : ActualEisensteinCubic.O →* ℂ) {I : Ideal ActualEisensteinCubic.O}
    (hI : ¬Squarefree I) : columnWeight Ψ I = 0 := by
  simp [columnWeight,squarefreeGaussCoefficient,hI]

theorem weighted_column_support (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X≤D)
    {I : Ideal ActualEisensteinCubic.O}
    (hn : columnWeight (rowTwist Ψ m f z) I * W ((Ideal.absNorm I:ℝ)/X) ≠ 0) :
    I∈InitialMeanSquare.outsideSquarefreeIdeals S D := by
  have hc : columnWeight (rowTwist Ψ m f z) I ≠ 0 :=
    fun h=>hn (by rw [h,zero_mul])
  have hwindow : W ((Ideal.absNorm I:ℝ)/X) ≠ 0 :=
    fun h=>hn (by rw [h,mul_zero])
  have hI : I≠0 := fun h=>hc (by rw [h,columnWeight_zero])
  have hsf : Squarefree I := by
    by_contra h
    exact hc (columnWeight_zero_of_not_squarefree _ h)
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,?_⟩,hsf⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hI (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast ((div_le_iff₀ hX).mp (hW _ hwindow)).trans hD
  · intro P hP hPI
    exact hc (columnWeight_zero_of_mask Ψ m f z (hSp P hP) hPI (hm P hP))

end

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

theorem excludedGenerator_mem (S : Finset (Ideal ActualEisensteinCubic.O)) {P : Ideal ActualEisensteinCubic.O} (hP : P∈S) :
    excludedGenerator S∈P := by
  have hdiv : P∣∏Q∈S,Q := Finset.dvd_prod_of_mem (fun Q:Ideal ActualEisensteinCubic.O=>Q) hP
  have hm : idealGenerator (∏Q∈S,Q)∈Ideal.span {idealGenerator (∏Q∈S,Q)} :=
    Ideal.subset_span (by simp)
  rw [span_idealGenerator] at hm
  exact (Ideal.dvd_iff_le.mp hdiv) hm

theorem excludedGenerator_not_mem_pool (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P)
    (i : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)) :
    excludedGenerator S∉i.val := by
  intro hm
  have hprime : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hspan : Ideal.span {excludedGenerator S} ≤ i.val :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
  change Ideal.span {idealGenerator (∏Q∈S,Q)} ≤ i.val at hspan
  rw [span_idealGenerator] at hspan
  have hdiv : i.val∣∏Q∈S,Q := Ideal.dvd_iff_le.mpr hspan
  obtain ⟨P,hPS,hPi⟩ := (hprime.dvd_finsetProd_iff (fun Q:Ideal ActualEisensteinCubic.O=>Q)).mp hdiv
  have heq : i.val=P := (prime_dvd_prime_iff_eq hprime (hSp P hPS)).mp hPi
  obtain ⟨I,hI,hfactor⟩ := mem_primePool_iff.mp i.property
  have ho : I∈outsideIdealsUpTo S D := (Finset.mem_filter.mp hI).1
  have hd : i.val∣I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hfactor
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P hPS (heq ▸ hd)

theorem outside_pool_fixed_mask (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (T : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D))) :
    rowCoprimeMask (fun i=>Ideal.span {poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D) i})
      T (excludedGenerator S) = 1 := by
  unfold rowCoprimeMask
  rw [if_neg]
  rintro ⟨i,hi,hmem⟩
  change excludedGenerator S ∈ Ideal.span {poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D) i} at hmem
  rw [poolPrimary_span _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)] at hmem
  exact excludedGenerator_not_mem_pool S D hSp i hmem

theorem canonicalSourceCoefficient_fixed_mask {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i}) (Ψ : ActualEisensteinCubic.O →* ℂ) (m c f : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (T : Finset ι)
    (hc : rowCoprimeMask (fun i=>Ideal.span {p i}) T c=1) :
    canonicalSourceCoefficient p hp hcop hg Ψ (m*c) f H T =
      canonicalSourceCoefficient p hp hcop hg Ψ m f H T := by
  simp only [canonicalSourceCoefficient,FirstPassCubeLabels.mask_mul _ hg,hc,mul_one]

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open CompletedGauss hiding O

theorem cubeIdeal_cubeIndex (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) (hB : B≠0)
    (hcover : ∀P∈UniqueFactorizationMonoid.normalizedFactors B,P∈primePool F) :
    cubeIdeal F (cubeIndex F B) = B := by
  have hsub : (UniqueFactorizationMonoid.normalizedFactors B).toFinset ⊆ primePool F := by
    intro P hP
    exact hcover P (Multiset.mem_toFinset.mp hP)
  calc
    _ = ∏P∈primePool F,P^(UniqueFactorizationMonoid.normalizedFactors B).count P := by
      simp only [cubeIdeal,cubeIndex_apply]
      exact Finset.prod_coe_sort (s := primePool F)
        (f := fun P:Ideal ActualEisensteinCubic.O=>P^(UniqueFactorizationMonoid.normalizedFactors B).count P)
    _ = (UniqueFactorizationMonoid.normalizedFactors B).prod :=
      (Finset.prod_multiset_count_of_subset _ _ hsub).symm
    _ = B := Ideal.prod_normalizedFactors_eq_self hB

theorem cubeIndex_inj (F : Finset (Ideal ActualEisensteinCubic.O)) (B C : Ideal ActualEisensteinCubic.O) (hB : B≠0) (hC : C≠0)
    (hb : ∀P∈UniqueFactorizationMonoid.normalizedFactors B,P∈primePool F)
    (hc : ∀P∈UniqueFactorizationMonoid.normalizedFactors C,P∈primePool F)
    (heq : cubeIndex F B = cubeIndex F C) : B=C := by
  have he := congrArg (cubeIdeal F) heq
  rwa [cubeIdeal_cubeIndex F B hB hb,cubeIdeal_cubeIndex F C hC hc] at he

theorem outside_cubeIdeal_cubeIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    {B : Ideal ActualEisensteinCubic.O} (hB : B∈outsideIdealsUpTo S D) :
    cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D)
      (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D) B) = B := by
  exact cubeIdeal_cubeIndex _ B (outsideIdealsUpTo_ne_bot S D B hB)
    (InitialMeanSquare.outside_factors_mem_pool S D hB)

theorem sum_outside_cubeIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (a : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑B∈outsideIdealsUpTo S D,a B) =
      ∑v∈(outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)),
        a (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro B hB
    rw [outside_cubeIdeal_cubeIndex S D hB]
  · intro B hB C hC he
    exact cubeIndex_inj _ B C (outsideIdealsUpTo_ne_bot S D B hB)
      (outsideIdealsUpTo_ne_bot S D C hC)
      (InitialMeanSquare.outside_factors_mem_pool S D hB)
      (InitialMeanSquare.outside_factors_mem_pool S D hC) he

theorem cubeIdeal_ne_zero (F : Finset (Ideal ActualEisensteinCubic.O)) (v : primePool F →₀ ℕ) :
    cubeIdeal F v ≠ 0 := by
  unfold cubeIdeal
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (NeZero.ne i.val))

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

theorem summand_cube_support (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D)
    (I B : Ideal ActualEisensteinCubic.O) (hn : summand (rowTwist Ψ m f z) W X I B≠0) :
    B∈outsideIdealsUpTo S D := by
  have hI : I≠0 := fun h=>hn (by rw [h,summand_zero_left])
  have hB : B≠0 := fun h=>hn (by rw [h,summand_zero_right])
  have hw : W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X)≠0 :=
    fun h=>hn (summand_zero_window _ W X I B h)
  have hsize := (div_le_iff₀ hX).mp (hW _ hw)
  have hb := (triple_scale_bounds (Ideal.absNorm I:ℝ) (Ideal.absNorm B:ℝ) 1
    (norm_at_least_one I hI) (norm_at_least_one B hB) (by norm_num)).2.1
  simp only [one_pow,mul_one] at hb
  apply mem_outsideIdealsUpTo.mpr
  refine ⟨?_,?_,?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hB (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast (hb.trans hsize).trans hD
  · intro P hP hPB
    have hz := cubeWeight_zero_of_prime_mask Ψ m f z (hSp P hP) hPB (hm P hP)
    exact hn (by simp only [summand,hz,mul_zero,zero_mul])

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CanonicalLogEnergy
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
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

theorem activeCubeExponents_norm_bound
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeExponents S D b X) :
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ max 1 (b*X) := by
  have hcube := (Finset.mem_filter.mp hv).2
  have hN := norm_at_least_one _ (cubeIdeal_ne_zero (InitialMeanSquare.outsideSquarefreeIdeals S D) v)
  let n := (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)
  have hone : 1 ≤ n := hN
  have hnn : n ≤ n^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (show 0 ≤ n^2+n by positivity)]
  exact (hnn.trans hcube).trans (le_max_right _ _)

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

theorem activeCubeLogIndex_mem (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeExponents S D b X) : cubeLogIndex S D v ∈ cubeLogRange b X := by
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact normLogBin_mono
    (lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v)))
    (activeCubeExponents_norm_bound S D b X v hv)

theorem sum_activeCubeLogBins {M : Type*} [AddCommMonoid M]
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (a : (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) → M) :
    (∑ v ∈ activeCubeExponents S D b X, a v) =
      ∑ j ∈ cubeLogRange b X, ∑ v ∈ activeCubeLogBin S D b X j, a v := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun v hv => activeCubeLogIndex_mem S D b X v hv) a

end CanonicalRowCompletion

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian
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

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O

theorem norm_add_sum_sq_le {κ : Type*} (s : Finset κ) (a : ℂ) (b : κ → ℂ) :
    ‖a + ∑ k ∈ s, b k‖^2 ≤ 2*(‖a‖^2 + s.card*∑ k ∈ s, ‖b k‖^2) := by
  have hs : ‖∑ k ∈ s, b k‖^2 ≤ (s.card : ℝ)*∑ k ∈ s, ‖b k‖^2 := by
    calc
      _ ≤ (∑ k ∈ s, ‖b k‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one]
          using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun k => ‖b k‖)
  have ha := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a (∑ k ∈ s, b k)) 2
  nlinarith [sq_nonneg (‖a‖ - ‖∑ k ∈ s, b k‖)]

end CanonicalRowCompletion

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Completion
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss

local notation "Eis" => ActualEisensteinCubic.O

theorem markedExpandedTerm_finite_support (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite := by
  apply (finite_support_expandedTerm Ψ W hW X hX).subset
  intro p hp hz
  apply hp
  simp only [markedExpandedTerm, hz, zero_mul]

theorem markedExpandedTerm_scale (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      (summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J * d (H ^ 3 * (I * J ^ 3))) =
      markedExpandedTerm Ψ W X d I H J := by
  rw [← mul_assoc, expandedTerm_scale]
  unfold markedExpandedTerm
  congr 2
  ring

theorem weighted_markedCompletedT_reopen (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (H : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) =
      ∑' I : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J := by
  simp only [markedCompletedT, ← tsum_mul_left, markedExpandedTerm_scale]

theorem marked_cube_inner_inverse (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X)
    (d : Ideal Eis → ℂ) (I : Ideal Eis) :
    (∑' H : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J) =
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let f : Ideal Eis → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X) * d (I * B ^ 3)
  have heq (H J : Ideal Eis) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        markedExpandedTerm Ψ W X d I H J := by
    simp only [f, markedExpandedTerm, expandedTerm, map_mul, Nat.cast_mul, mul_pow,
      mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal Eis × Ideal Eis => (I, p)) ⁻¹'
      Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
        markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  simpa only [heq, f, map_one, Nat.cast_one, one_pow, mul_one] using hgeneric

theorem marked_cube_inverse_vstar (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A))) =
    ∑' I : Ideal Eis, (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let F : Ideal Eis × Ideal Eis × Ideal Eis → ℂ :=
    fun p => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2
  have hF : Summable F :=
    summable_of_hasFiniteSupport (markedExpandedTerm_finite_support Ψ W hW X hX d)
  let e : (Ideal Eis × Ideal Eis × Ideal Eis) ≃ (Ideal Eis × Ideal Eis × Ideal Eis) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal Eis, ∑' I : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      simp only [weighted_markedCompletedT_reopen]
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F p := e.tsum_eq F
    _ = ∑' I : Ideal Eis, ∑' H : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_cube_inner_inverse Ψ W hW X hX d)

theorem marked_cube_inverse (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal Eis, columnWeight Ψ I * d I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) := by
  rw [marked_cube_inverse_vstar Ψ W hW X hX d, ← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [vstar_source_normalization Ψ W X hX I]
  ring

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CompletionSplit
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem marked_cube_inverse_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (Function.support (fun H : Ideal O =>
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
        markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H^3*A)))).Finite := by
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  apply (hf.image (fun p => p.2.1)).subset
  intro H hH
  by_contra hn
  have hzero : ∀ I J, markedExpandedTerm Ψ W X d I H J = 0 := by
    intro I J
    by_contra hz
    exact hn ⟨(I, H, J), hz, rfl⟩
  apply hH
  dsimp only
  rw [weighted_markedCompletedT_reopen]
  simp only [hzero, tsum_zero]

theorem marked_large_cube_inner_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) (I : Ideal O) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0) =
    ∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)*
      Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm B : ℝ)^3/X)*d (I*B^3)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ (H*J)*f (H*J)=markedExpandedTerm Ψ W X d I H J := by
    simp only [f,markedExpandedTerm,expandedTerm,map_mul,Nat.cast_mul,mul_pow,mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal O × Ideal O => markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I,p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hg := large_cube_convolution H₀ (cubeWeight Ψ) (cubeWeight_zero Ψ) f (by simpa only [heq] using hp)
  rw [show (∑' H : Ideal O, ∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0)=
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*cubeWeight Ψ B*f B by simpa only [heq] using hg]
  apply tsum_congr
  intro B
  dsimp [f,summand]
  ring

theorem marked_large_cube_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (∑' H : Ideal O, if H₀ ≤ (Ideal.absNorm H : ℝ) then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A)) else 0) =
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.2.1 : ℝ) then markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2 else 0
  have hF : Summable F := summable_of_hasFiniteSupport
    ((markedExpandedTerm_finite_support Ψ W hW X hX d).subset (by
      intro p hp
      by_contra hn
      have he : markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2=0 := not_ne_iff.mp hn
      exact hp (by simp [F,he])))
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1,p.1,p.2.2)
    invFun := fun p => (p.2.1,p.1,p.2.2)
    left_inv := by rintro ⟨I,H,J⟩;rfl
    right_inv := by rintro ⟨I,H,J⟩;rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O,∑' I : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0 := by
      apply tsum_congr
      intro H
      by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
      · simp only [if_pos h,weighted_markedCompletedT_reopen]
      · simp only [if_neg h,tsum_zero]
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F p := e.tsum_eq F
    _ = ∑' I : Ideal O,∑' H : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0 := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_large_cube_inner_reopen Ψ W hW X H₀ hX d)

theorem marked_completed_cube_inverse_split (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (Real.sqrt X : ℂ)⁻¹*(∑' I : Ideal O,columnWeight Ψ I*d I*W ((Ideal.absNorm I : ℝ)/X)) =
    (∑' H : Ideal O, if (Ideal.absNorm H : ℝ)<H₀ then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A)) else 0) +
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let f := fun H : Ideal O => (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A))
  have hf := marked_cube_inverse_finite_support Ψ W hW X hX d
  have hs : Summable (fun H : Ideal O => if (Ideal.absNorm H : ℝ)<H₀ then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  have hl : Summable (fun H : Ideal O => if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  rw [marked_cube_inverse Ψ W hW X hX d,←marked_large_cube_reopen Ψ W hW X H₀ hX d]
  change (∑' H,f H)=(∑' H,if (Ideal.absNorm H : ℝ)<H₀ then f H else 0)+
    ∑' H,if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0
  rw [← hs.tsum_add hl]
  apply tsum_congr
  intro H
  by_cases h : (Ideal.absNorm H : ℝ)<H₀
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CompletionSupport
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem marked_large_cube_sum_comm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0<X) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3)) =
      ∑'B:Ideal O,∑'I:Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let a : Ideal O×Ideal O → ℂ := fun p=>largeCubeCoefficient H₀ p.2*summand Ψ W X p.1 p.2*d (p.1*p.2^3)
  have hf : (Function.support a).Finite :=
    (completedT_finite_support Ψ W hW X hX).subset (by
      intro p hp
      exact fun h=>hp (by simp only [a,h,mul_zero,zero_mul]))
  have hs : Summable a := summable_of_hasFiniteSupport hf
  let e := Equiv.prodComm (Ideal O) (Ideal O)
  have ht : Summable (fun p=>a (e p)) := e.summable_iff.mpr hs
  calc
    _ = ∑'p:Ideal O×Ideal O,a p := hs.tsum_prod.symm
    _ = ∑'p:Ideal O×Ideal O,a (e p) := (e.tsum_eq a).symm
    _ = _ := ht.tsum_prod

theorem marked_large_cube_sum_finite (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B*summand (rowTwist Ψ m f z) W X I B*d (I*B^3)) =
      ∑B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑'I:Ideal O,summand (rowTwist Ψ m f z) W X I B*d (I*B^3) := by
  rw [marked_large_cube_sum_comm _ W hWc X H₀ hX d]
  simp only [mul_assoc, tsum_mul_left]
  apply tsum_eq_sum
  intro B hB
  have hz : ∀I:Ideal O,summand (rowTwist Ψ m f z) W X I B=0 := by
    intro I
    by_contra hn
    exact hB (summand_cube_support S D hSp Ψ m f z hm W b X hX hW hD I B hn)
  simp only [hz,tsum_zero,mul_zero,zero_mul]

theorem marked_inner_completed_sum (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (B : Ideal O) (hB : B≠0) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,summand Ψ W X I B*d (I*B^3)) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))*d (I*B^3) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal O) : summand Ψ W X I B =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        (columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
    have harg : (Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X =
        (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3) := by
      rw [div_div_eq_mul_div]
    have hn := vstar_source_normalization Ψ W (X/(Ideal.absNorm B:ℝ)^3) hY I
    calc
      _ = cubeWeight Ψ B * (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ) *
          Vstar W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
        rw [summand,harg]
        ring
      _ = _ := by rw [hn]; ring
  simp_rw [ht]
  simp only [mul_assoc, tsum_mul_left]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CompletePool
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem marked_selected_column_sum (F : Finset (Ideal O))
    (hF : ∀I∈F,CanonicalQuadraticSieve.Admissible I)
    (Ψ : O →* ℂ) (m f z : O) (W : ℕ → ℂ) (d : Ideal O → ℂ) :
    let p := CanonicalQuadraticSieve.poolPrimary F
    let hp := CanonicalQuadraticSieve.poolPrimary_ne_zero F hF
    letI : ∀i:ConcretePrimeRowBridge.primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i=>by rw [CanonicalQuadraticSieve.poolPrimary_span F hF i]; infer_instance
    let hcop := CanonicalQuadraticSieve.poolPrimary_coprime F hF
    let hg := CanonicalQuadraticSieve.poolPrimary_good F hF
    (∑I∈F,columnWeight (rowTwist Ψ m f z) I * W (Ideal.absNorm I)*d I) =
      ∑S∈(Finset.univ:Finset (ConcretePrimeRowBridge.primePool F)).powerset,
        canonicalSourceCoefficient p hp hcop hg Ψ m f (fun T=>InitialMeanSquare.selectedIdealTest F W T*d (∏i∈T,i.val)) S *
          finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  dsimp only
  let : ∀i:ConcretePrimeRowBridge.primePool F,
      (Ideal.span {CanonicalQuadraticSieve.poolPrimary F i}).IsMaximal :=
    fun i=>by rw [CanonicalQuadraticSieve.poolPrimary_span F hF i]; infer_instance
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI=>(hF I hI).2.1)]
  apply Finset.sum_congr rfl
  intro S hS
  have hspan : (Ideal.span {∏i∈S,CanonicalQuadraticSieve.poolPrimary F i}) = ∏i∈S,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>CanonicalQuadraticSieve.poolPrimary_span F hF i)
  have hpr (i:ConcretePrimeRowBridge.primePool F) :
      ConcretePrimeRowBridge.goodLambda^2∣CanonicalQuadraticSieve.poolPrimary F i-1 :=
    (primaryPrime_spec i.val (CanonicalQuadraticSieve.poolPrimary_ne_zero F hF i)).2.2.2
  have h := columnWeight_finset (CanonicalQuadraticSieve.poolPrimary F)
    (CanonicalQuadraticSieve.poolPrimary_ne_zero F hF)
    (CanonicalQuadraticSieve.poolPrimary_coprime F hF)
    (CanonicalQuadraticSieve.poolPrimary_good F hF) hpr S Ψ m f z
    (fun T=>InitialMeanSquare.selectedIdealTest F W T*d (∏i∈T,i.val))
  rw [hspan] at h
  rw [←h]
  unfold InitialMeanSquare.selectedIdealTest
  split_ifs <;> simp ; ring

theorem marked_weighted_column_tsum_eq (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀ P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀ P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0 → t≤b) (hD : b*X≤D) (d : Ideal O → ℂ) :
    (∑' I:Ideal O,columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)*d I) =
      ∑ I∈InitialMeanSquare.outsideSquarefreeIdeals S D,
        columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)*d I := by
  apply tsum_eq_sum
  intro I hI
  have hz : columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)=0 := by
    by_contra hn
    exact hI (weighted_column_support S D hSp Ψ m f z hm W b X hX hW hD hn)
  rw [hz,zero_mul]

theorem marked_complete_pool_eq_global (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0 → t≤b) (hD : b*X≤D) (d : Ideal O → ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    fixedChildRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ Ψ m
      (fun T=>W (primeProductNorm (poolPrimary F) T/X)*d (∏i∈T,i.val)) f z =
    ∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*
      W ((Ideal.absNorm I:ℝ)/X)*d I := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  symm
  rw [marked_weighted_column_tsum_eq S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W b X hX hW hD d]
  have he := marked_selected_column_sum F hF Ψ (m*excludedGenerator S) f z (fun n=>W (n/X)) d
  dsimp only at he
  rw [he]
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro T hT
  rw [canonicalSourceCoefficient_fixed_mask _ _ _ _ Ψ m (excludedGenerator S) f _ T
    (outside_pool_fixed_mask S D hbad hSp T)]
  have ht := InitialMeanSquare.selectedIdealTest_outside S D hbad hSp W b X hX hW hD T
  simp only [canonicalSourceCoefficient,secondChildColumn]
  rw [ht]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ReopenedMarks
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_span_primeProduct (S : Finset ι) (v : ι→ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣Ideal.span {primeProduct p S v} ↔ i∈S ∧ 0<v i := by
  simp only [primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
  rw [←dvd_iff_emultiplicity_pos,primeIdealProduct_emultiplicity (fun i=>Ideal.span {p i}) hinj]
  by_cases hi : i∈S <;> simp [hi]

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_reopened_index (S : Finset ι) (v : ι→₀ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣(Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 ↔
      i∈S∪v.support := by
  have hi : Prime (Ideal.span {p i}:Ideal O) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have hs := prime_dvd_span_primeProduct p hinj S (fun _=>1) i
  simp only [primeProduct,pow_one,Nat.zero_lt_one,and_true] at hs
  rw [hi.dvd_mul,hi.dvd_pow_iff_dvd (by decide : (3:ℕ)≠0),hs,
    prime_dvd_span_primeProduct p hinj v.support v i,Finset.mem_union]
  have hv : i∈v.support ↔ 0<v i := by rw [Finsupp.mem_support_iff]; omega
  tauto

include hinj in

omit [DecidableEq σ] in
theorem reopened_whole_mark_divisibility (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
    ∏j∈slots,∑i∈lists j,if (Ideal.span {p i}:Ideal O)∣
      (Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 then a j i else 0 := by
  unfold primeMark primeSlot
  simp_rw [prime_dvd_reopened_index p hinj]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem complete_pool_mark {σ : Type*} [DecidableEq σ]
    (F : Finset (Ideal O)) (hF : ∀ I∈F,Admissible I)
    (slots : Finset σ) (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (T : Finset (primePool F)) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val) =
      primeMark slots lists a T := by
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hinj : Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j h
    dsimp only at h
    rw [poolPrimary_span F hF i,poolPrimary_span F hF j] at h
    exact Subtype.ext h
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T 0
  simp only [Finsupp.support_zero,Finset.union_empty,primeProduct,Finset.prod_empty,
    Ideal.span_singleton_one,←Ideal.one_eq_top,one_pow,mul_one] at he
  have hspan : Ideal.span {∏i∈T,poolPrimary F i}=∏i∈T,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  rw [hspan] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem finiteCanonicalMarkedRow_complete_global {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X =
    ∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a I*W ((Ideal.absNorm I:ℝ)/X) := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b X hX hW hD
    (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)
  dsimp only at he
  have hmark : (fun T:Finset (primePool F)=>W (primeProductNorm (poolPrimary F) T/X)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val)) =
      (fun T=>primeMark slots lists a T*W (primeProductNorm (poolPrimary F) T/X)) := by
    funext T
    rw [complete_pool_mark F hF slots lists a T,mul_comm]
  rw [hmark] at he
  unfold finiteCanonicalMarkedRow
  calc
    _ = _ := he
    _ = _ := tsum_congr (fun I=>by ring)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CompletedReopening
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem outsideCanonicalMarkedRow_cube_split {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      ∑ B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑' I:Ideal O,summand Ψrow W X I B*mark (I*B^3) := by
  dsimp only
  unfold outsideCanonicalMarkedRow
  rw [finiteCanonicalMarkedRow_complete_global S D hbad hSp Ψ m f z W b X hX hW hD]
  rw [marked_completed_cube_inverse_split _ W hWc X H₀ hX]
  rw [marked_large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]

theorem outsideCanonicalMarkedRow_reopened {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      ∑ B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B*cubeWeight Ψrow B*
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹)*
        ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))*mark (I*B^3) := by
  rw [outsideCanonicalMarkedRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  rw [marked_inner_completed_sum _ W X hX B (outsideIdealsUpTo_ne_bot S D B hB)]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ReopenedOriginalRow
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem original_marked_split_to_bins {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool F=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      markedReopenedCubeBin S D ((outsideIdealsUpTo S D).image (cubeIndex F)) Ψ m f z W X H₀ slots lists a := by
  rw [outsideCanonicalMarkedRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  rw [sum_outside_cubeIndex S D]
  rfl

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ReopenedBins
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem marked_column_zero_of_subunit (Ψ : O→*ℂ) (W : ℝ→ℂ) (b Y : ℝ)
    (hY : 0<Y) (hW : ∀ t,W t≠0→t≤b) (hsub : b*Y<1) (mark : Ideal O→ℂ) :
    (∑' I:Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I:ℝ)/Y)*mark I)=0 := by
  suffices hz : ∀ I:Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I:ℝ)/Y)*mark I=0 by
    simp only [hz,tsum_zero]
  intro I
  by_cases hI : I=0
  · simp only [hI,columnWeight_zero,zero_mul]
  have hw : W ((Ideal.absNorm I:ℝ)/Y)=0 := by
    by_contra hn
    have hh := (div_le_iff₀ hY).mp (hW _ hn)
    have hone := norm_at_least_one I hI
    linarith
  simp only [hw,mul_zero,zero_mul]

variable {σ : Type*} [DecidableEq σ]
  (S : Finset (Ideal O)) (D : ℕ)
  (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X H₀ : ℝ)
  (slots : Finset σ)
  (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
  (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)

theorem markedReopenedCubeBin_eq_active (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) :
    markedReopenedCubeBin S D
      ((outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      Ψ m f z W X H₀ slots lists a =
    markedReopenedCubeBin S D (activeCubeExponents S D b X) Ψ m f z W X H₀ slots lists a := by
  unfold markedReopenedCubeBin activeCubeExponents
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hlarge : b*X<(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3 := by
    exact lt_of_not_ge (fun hh=>hn (Finset.mem_filter.mpr ⟨hv,hh⟩))
  have hN : 0<(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ) :=
    lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  have hsub : b*(X/(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3)<1 := by
    rw [←mul_div_assoc]
    exact (div_lt_one (pow_pos hN _)).mpr hlarge
  rw [marked_column_zero_of_subunit _ W b _ (div_pos hX (pow_pos hN _)) hW hsub,mul_zero]

theorem markedReopenedCubeBin_log_bins :
    markedReopenedCubeBin S D (activeCubeExponents S D b X) Ψ m f z W X H₀ slots lists a =
    ∑ j∈cubeLogRange b X,
      markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a := by
  unfold markedReopenedCubeBin
  dsimp only
  exact sum_activeCubeLogBins S D b X _

theorem original_marked_reopened_binned (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D) :
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
    markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a) +
    ∑ j∈cubeLogRange b X,
      markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a := by
  rw [original_marked_split_to_bins S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [markedReopenedCubeBin_eq_active S D Ψ m f z W b X H₀ slots lists a hX hW,
    markedReopenedCubeBin_log_bins]
  rfl

theorem original_marked_binned_energy_oai (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D) :
    ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 ≤
    2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2 +
    (cubeLogRange b X).card*∑ j∈cubeLogRange b X,
      ‖markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a‖^2) := by
  have hs := norm_add_sum_sq_le (cubeLogRange b X)
    (markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a))
    (fun j=>markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a)
  rw [←original_marked_reopened_binned S D Ψ m f z W b X H₀ slots lists a hbad hSp hWc hX hW hD] at hs
  have hn : ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 =
      X*‖(Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X),
      mul_pow,inv_pow,Real.sq_sqrt hX.le]
    field_simp
  rw [hn]
  convert (preTransparency := .instances) mul_le_mul_of_nonneg_left hs hX.le using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.InverseMoment.original_marked_binned_energy_oai.{u_1} := @OAI.SevenEighths.InverseMoment.original_marked_binned_energy_oai.{u_1}
