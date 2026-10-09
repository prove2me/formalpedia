-- Prove2me | solution 1 for OAI.SevenEighths.InverseReflectedPhase.original_surviving_energy_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:42:18.30244+00:00
-- url     : https://prove2.me/submissions/0b112212-296e-4d82-baa0-354ec50a3a62

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B026
import Definitions.Def_OAIHecke78B028

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.PowerfulParts
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
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid

theorem rowPowerfulPart_ne_zero (I : Ideal O) : rowPowerfulPart I≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem rowPowerfulPart_powerful (I : Ideal O) : PowerfulIdeal (rowPowerfulPart I) := by
  refine ⟨rowPowerfulPart_ne_zero I,?_⟩
  intro P hP
  rw [normalizedFactors_rowPowerfulPart] at hP ⊢
  have hp := (Multiset.mem_filter.mp hP).2
  rw [Multiset.count_filter,if_pos hp]
  exact hp

end

open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid

theorem squarefreeMaskPart_ne_zero (I R : Ideal O) : squarefreeMaskPart I R≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem rowResidualPart_norm (I R : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowResidualPart I R):ℝ)=(Ideal.absNorm I:ℝ)/
      ((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I R):ℝ)) := by
  have hp : (Ideal.absNorm (rowPowerfulPart I):ℝ)≠0 := by
    exact_mod_cast (fun hz => rowPowerfulPart_ne_zero I (Ideal.absNorm_eq_zero_iff.mp hz))
  have ht : (Ideal.absNorm (rowMaskPart I R):ℝ)≠0 := by
    exact_mod_cast (fun hz => squarefreeMaskPart_ne_zero (rowSimplePart I) R (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (eq_div_iff (mul_ne_zero hp ht)).mpr
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (row_powerful_mask_residual_product I R hI)
  simpa only [map_mul,Nat.cast_mul,mul_comm] using he

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.NormalizedMass
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
namespace CompletedGauss

open ActualEisensteinCubic UniqueFactorizationMonoid

theorem prime_square_dvd_powerful (I P : Ideal O) (hI : PowerfulIdeal I)
    (hP : Prime P) (hd : P∣I) : P^2∣I := by
  have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI.1).mpr ⟨hP,hd⟩
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero 2 hP.ne_zero) hI.1).mpr
  rw [normalizedFactors_pow,normalizedFactors_irreducible hP.irreducible,normalize_eq]
  apply Multiset.le_iff_count.mpr
  intro Q
  by_cases hQP : Q=P
  · subst Q
    simpa using hI.2 P hm
  · simp [hQP]

theorem nonresidual_prime_square_dvd (I Q P : Ideal O) (hI : I≠0) (hP : Prime P)
    (hd : P∣I) (hr : ¬P∣rowResidualPart I Q) :
    P^2∣rowPowerfulPart I*(rowMaskPart I Q)^2 := by
  have hh : P∣rowPowerfulPart I*rowMaskPart I Q := by
    rw [←row_powerful_mask_residual_product I Q hI] at hd
    exact (hP.dvd_mul.mp hd).resolve_right hr
  rcases hP.dvd_mul.mp hh with ha|ht
  · exact dvd_mul_of_dvd_left (prime_square_dvd_powerful _ _ (rowPowerfulPart_powerful I) hP ha) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ht 2) _

theorem nonresidual_gain_product_dvd {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) :
    (∏i,nonresidualGain I (P i)) ∣ rowPowerfulPart I*(rowMaskPart I Q)^2*Q := by
  apply Fintype.prod_dvd_of_coprime
  · intro i j hij
    change IsCoprime (nonresidualGain I (P i)) (nonresidualGain I (P j))
    unfold nonresidualGain
    by_cases hi : P i∣I
    · rw [if_pos hi]
      by_cases hj : P j∣I
      · rw [if_pos hj]
        exact (hcop hij).pow
      · rw [if_neg hj]
        exact (hcop hij).pow_left
    · rw [if_neg hi]
      by_cases hj : P j∣I
      · rw [if_pos hj]
        exact (hcop hij).pow_right
      · rw [if_neg hj]
        exact hcop hij
  · intro i
    have hp : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
    by_cases hi : P i∣I
    · rw [nonresidualGain,if_pos hi]
      exact dvd_mul_of_dvd_left (nonresidual_prime_square_dvd I Q (P i) hI hp hi (hres i)) Q
    · rw [nonresidualGain,if_neg hi]
      exact dvd_mul_of_dvd_right ((hp.dvd_mul.mp (hpool i)).resolve_left hi) _

open ActualEisensteinCubic UniqueFactorizationMonoid

theorem reflectionConductorCost_eq_prod {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0) (j : ι→ℕ) (e : ι→Fin 3) :
    reflectionConductorCost P j e=∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (j i) (e i) := by
  have hn i : (Ideal.absNorm (P i):ℝ)≠0 := by
    exact_mod_cast (fun hz => hP i (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [reflectionConductorCost,reflectionExtractedDivisor,map_prod,Nat.cast_prod,
    ←Finset.prod_pow,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hj4 : j i=4
  · rw [hj4]
    generalize he : e i=v
    fin_cases v <;> simp [reflectionExtractedPrime,reflectionLocalCost] <;> field_simp
  · by_cases hj0 : j i=0
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj0]
      field_simp
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj4,hj0]

theorem reflectionLocalCost_nonneg (q : ℝ) (hq : 0≤q) (j : ℕ) (e : Fin 3) :
    0≤ reflectionLocalCost q j e := by
  unfold reflectionLocalCost
  split_ifs <;> positivity

theorem reflectionLocalCost_le_square (q : ℝ) (hq : 1≤q) (j : ℕ) (e : Fin 3) :
    reflectionLocalCost q j e≤q^2 := by
  have hq0 : 0<q := by linarith
  have hq2 : 1≤q^2 := one_le_pow₀ hq
  unfold reflectionLocalCost
  split_ifs
  · exact (div_le_one (by positivity)).mpr hq2 |>.trans hq2
  · nlinarith
  · nlinarith
  · rfl

theorem reflectionLocalCost_le_single (q : ℝ) (hq : 1≤q) (j : ℕ) (e : Fin 3)
    (hj : j=0 ∨ j=4) : reflectionLocalCost q j e≤q := by
  have hq0 : 0<q := by linarith
  rcases hj with rfl|rfl
  · simp [reflectionLocalCost]
  · simp only [reflectionLocalCost,ite_true]
    split_ifs
    · exact ((div_le_one (by positivity)).mpr (one_le_pow₀ hq)).trans hq
    · rfl

theorem completedLocalExponent_of_not_dvd (I F P : Ideal O) (hI : I≠0) (_hP : Prime P)
    (hn : ¬P∣I) : completedLocalExponent I F P=0 ∨ completedLocalExponent I F P=4 := by
  have hm : P∉normalizedFactors I := by
    intro h
    exact hn ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mp h).2
  simp only [completedLocalExponent,Multiset.count_eq_zero.mpr hm,zero_add]
  split_ifs <;> norm_num

theorem reflectionLocalCost_le_gain (I F P : Ideal O) (hI : I≠0) (hP : Prime P) (e : Fin 3) :
    reflectionLocalCost (Ideal.absNorm P:ℝ) (completedLocalExponent I F P) e≤
      (Ideal.absNorm (nonresidualGain I P):ℝ) := by
  have hq : 1≤(Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  by_cases hd : P∣I
  · rw [nonresidualGain,if_pos hd,map_pow,Nat.cast_pow]
    exact reflectionLocalCost_le_square _ hq _ _
  · rw [nonresidualGain,if_neg hd]
    exact reflectionLocalCost_le_single _ hq _ _ (completedLocalExponent_of_not_dvd I F P hI hP hd)

theorem reflectionConductorCost_bound {ι : Type*} [Fintype ι]
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e≤
      (Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ)^2*(Ideal.absNorm Q:ℝ) := by
  rw [reflectionConductorCost_eq_prod P (fun i => NeZero.ne (P i))]
  have hfirst : (∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (completedLocalExponent I F (P i)) (e i))≤
      (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ) := by
    rw [map_prod,Nat.cast_prod]
    exact Finset.prod_le_prod (fun i _ => reflectionLocalCost_nonneg _ (Nat.cast_nonneg _) _ _)
      (fun i _ => reflectionLocalCost_le_gain I F (P i) hI (Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance) (e i))
  apply hfirst.trans
  have hd := nonresidual_gain_product_dvd I Q hI P hcop hpool hres
  have hN : 0<Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hne := mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
      (pow_ne_zero 2 (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))) hQ
    exact hne (Ideal.absNorm_eq_zero_iff.mp hz)
  have hb := Nat.le_of_dvd hN (map_dvd Ideal.absNorm hd)
  have hr : (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ)≤
      (Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q):ℝ) := by exact_mod_cast hb
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hr

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ReflectedBranches
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
namespace CompletedGauss

section
open ActualEisensteinCubic LocalReflectionBrackets

theorem reflectionExtractedDivisor_ne_zero {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) :
    reflectionExtractedDivisor P j e v≠0 := by
  unfold reflectionExtractedDivisor
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  unfold reflectionExtractedPrime
  split_ifs
  · exact hP i
  · exact one_ne_zero

theorem reflectedBranch_divisibility {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (hcop : Pairwise (fun i k => IsCoprime (P i) (P k)))
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) (hne : reflectedBranch P hg j e n b≠0) :
    reflectionExtractedDivisor P j e 1∣Ideal.span {n} ∧
    reflectionExtractedDivisor P j e 2∣Ideal.span {b} ∧
    (∀i,j i=4 → e i=2 → n∉P i) := by
  have hn i : reflectedLocalPiece (P i) (hg i) (j i) (e i) n b≠0 :=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  have hmemn i (hj : j i=4) (he : e i=1) : n∈P i := by
    by_contra hz
    exact hn i (by simp [reflectedLocalPiece,exceptionalPiece,hj,he,hz])
  have hmemb i (hj : j i=4) (he : e i=2) : n∉P i ∧ b∈P i := by
    by_contra hz
    exact hn i (by simp [reflectedLocalPiece,exceptionalPiece,hj,he,hz])
  have hprod (v : Fin 3) (z : O)
      (hz : ∀i,(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) → z∈P i) :
      reflectionExtractedDivisor P j e v∣Ideal.span {z} := by
    unfold reflectionExtractedDivisor reflectionExtractedPrime
    apply Fintype.prod_dvd_of_coprime
    · intro i k hik
      change IsCoprime (if (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) then P i else 1)
        (if (j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0) then P k else 1)
      by_cases hi : (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0)
      · rw [if_pos hi]
        by_cases hk : (j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0)
        · rw [if_pos hk]
          exact hcop hik
        · rw [if_neg hk]
          exact isCoprime_one_right
      · rw [if_neg hi]
        exact isCoprime_one_left
    · intro i
      split_ifs with hi
      · rw [Ideal.dvd_iff_le,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
        exact hz i hi
      · exact one_dvd _
  refine ⟨hprod 1 n ?_,hprod 2 b ?_,fun i hj he => (hmemb i hj he).1⟩
  · intro i hi
    rcases hi with ⟨hj,he⟩|⟨hj,he⟩
    · exact hmemn i hj he
    · norm_num at he
  · intro i hi
    rcases hi with ⟨hj,he⟩|⟨hj,he⟩
    · exact (hmemb i hj he).2
    · ((try simp  at he) <;> norm_num  at he)

end

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open MeasureTheory Filter

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.DyadicKernel
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

open scoped BigOperators
namespace CompletedDyadic

theorem ramifiedScale_pos (ρ q : ℝ) (hρ : 0<ρ) (hq : 0<q) (m : ℕ) :
    0< ramifiedScale ρ q m := by unfold ramifiedScale; positivity

end CompletedDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CompletedDyadicRows
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
namespace CompletedGauss

section

open ActualEisensteinCubic

theorem two_pow_clog_le_double (n : ℕ) (hn : 1≤n) : 2^Nat.clog 2 n≤2*n := by
  by_cases h : n=1
  · simp [h]
  have hn1 : 1<n := lt_of_le_of_ne hn (Ne.symm h)
  have hl : 0<Nat.clog 2 n := Nat.clog_pos (by norm_num) hn1
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hn1
  have he : (Nat.clog 2 n).pred+1=Nat.clog 2 n := Nat.succ_pred_eq_of_pos hl
  calc
    _ = 2^(Nat.clog 2 n).pred*2 := by rw [←he,pow_succ]; rfl
    _ ≤ n*2 := Nat.mul_le_mul_right 2 hp.le
    _ = _ := Nat.mul_comm _ _

open ActualEisensteinCubic CanonicalQuadraticSieve

end
section

open CompletedDyadic

theorem completedRamifiedStep_gt_one : 1<completedRamifiedStep := by
  exact Real.one_lt_rpow (by norm_num) (by norm_num)

end

open ActualEisensteinCubic CanonicalQuadraticSieve

end CompletedGauss

open scoped BigOperators Classical SchwartzMap

open MeasureTheory
open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
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
open scoped Classical BigOperators Topology

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma dualIdealDyad_bounds (j : ℕ) (I : Ideal Eis) (hI : I∈dualIdealDyad j) :
    I≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^j := by
  obtain ⟨hn,hj⟩:= (mem_dualIdealDyad I j).mp hI
  have hu:=Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)
  have hl:=two_pow_clog_le_double (Ideal.absNorm I)
    (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn))
  rw [hj] at hu hl
  refine ⟨hn,?_,by exact_mod_cast hu⟩
  have he : (2:ℝ)^j≤2*(Ideal.absNorm I:ℝ):=by exact_mod_cast hl
  linarith

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.PeriodicRows
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

namespace CompletedGauss

section
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma completedReflectionPool_divides (I Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (P:completedReflectionPool I Q) : P.val∣I*Q :=
  ((mem_completedReflectionPool I Q P.val hI hQ).mp P.property).2.1

lemma completedReflectionPool_exponent_eq (I J F Q:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q)
    (P:completedReflectionPool I Q) :
    completedLocalExponent I F P.val=completedLocalExponent J F P.val := by
  rcases (mem_completedReflectionPool I Q P.val hI hQ).mp P.property with
    ⟨hP,hdiv,_,_,hres⟩
  exact (nonresidual_prime_transport I J F Q P.val hI hJ hP hA hT hdiv hres).2.2

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedThetaTwists
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

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma pool_divides (I Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (P:pool I Q Q0) : P.val∣I*Q :=
  completedReflectionPool_divides I Q hI hQ ⟨P.val,pool_subset I Q Q0 P.property⟩

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.FreePrimePools
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

section
open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma nonresidualPoolEquiv_exponent (R I F Q Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart R=rowPowerfulPart I) (hT:rowMaskPart R Q=rowMaskPart I Q)
    (P:FreeReflection.pool R Q Q0) :
    completedLocalExponent I F (nonresidualPoolEquiv R I Q Q0 hR hI hQ hA hT P).val=
      completedLocalExponent R F P.val :=
  (completedReflectionPool_exponent_eq R I F Q hR hI hQ hA hT
    ⟨P.val,FreeReflection.pool_subset R Q Q0 P.property⟩).symm

variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop hA hT

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

end

open scoped BigOperators Classical

end

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

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Widths
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma actual_ideal_norm_pos (I : Ideal Eis) (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))

theorem actual_residual_norm_width (I Q : Ideal Eis) (hI : I ≠ 0) :
    (Ideal.absNorm (rowResidualPart I Q) : ℝ) *
      (Ideal.absNorm (rowPowerfulPart I) : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  have hm : 1 ≤ (Ideal.absNorm (rowMaskPart I Q) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz =>
      squarefreeMaskPart_ne_zero (rowSimplePart I) Q (Ideal.absNorm_eq_zero_iff.mp hz))
  have he := congrArg (fun J : Ideal Eis => (Ideal.absNorm J : ℝ))
    (row_powerful_mask_residual_product I Q hI)
  simp only [map_mul, Nat.cast_mul] at he
  calc
    _ ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ) *
        (Ideal.absNorm (rowMaskPart I Q) : ℝ) * (Ideal.absNorm (rowResidualPart I Q) : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ) *
          (Ideal.absNorm (rowPowerfulPart I) : ℝ) by positivity)
      nlinarith [hh]
    _ = _ := he

theorem actual_common_width_charge {ι : Type*} [Fintype ι]
    (I F Q : Ideal Eis) (hI : I ≠ 0) (hQ : Q ≠ 0)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * Q)
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I Q) (e : ι → Fin 3) :
    (Ideal.absNorm (rowResidualPart I Q) : ℝ)^2 *
      reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e ≤
      (Ideal.absNorm I : ℝ)^2 / (Ideal.absNorm (rowPowerfulPart I) : ℝ) *
        (Ideal.absNorm Q : ℝ) := by
  have hp := actual_ideal_norm_pos (rowPowerfulPart I) (rowPowerfulPart_ne_zero I)
  have hm := actual_ideal_norm_pos (rowMaskPart I Q)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)
  have he := rowResidualPart_norm I Q hI
  calc
    _ ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ)^2 *
        ((Ideal.absNorm (rowPowerfulPart I) : ℝ) *
          (Ideal.absNorm (rowMaskPart I Q) : ℝ)^2 * (Ideal.absNorm Q : ℝ)) :=
      mul_le_mul_of_nonneg_left (reflectionConductorCost_bound I F Q hI hQ P hcop hpool hres e)
        (sq_nonneg _)
    _ = _ := by rw [he]; field_simp

theorem actual_common_width_charge_label_puncture {ι : Type*} [Fintype ι]
    (I F rho S : Ideal Eis) (hI : I ≠ 0) (hF : F ≠ 0) (hrho : rho ≠ 0) (hS : S ≠ 0)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (S * F * rho))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (S * F * rho)) (e : ι → Fin 3) :
    (Ideal.absNorm (rowResidualPart I (S * F * rho)) : ℝ)^2 *
      reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e ≤
      (Ideal.absNorm S : ℝ) *
        ((Ideal.absNorm I : ℝ)^2 / (Ideal.absNorm (rowPowerfulPart I) : ℝ)) *
        (Ideal.absNorm F : ℝ) * (Ideal.absNorm rho : ℝ) := by
  convert (preTransparency := .instances) actual_common_width_charge I F (S * F * rho) hI
    (mul_ne_zero (mul_ne_zero hS hF) hrho) P hcop hpool hres e using 1
  simp only [map_mul, Nat.cast_mul]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.TerminalWidths
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseTerminalWidths
open ActualEisensteinCubic CompletedGauss UniqueFactorizationMonoid
open InverseMoment CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma norm_one_le (I : Ideal O) (hI : I ≠ 0) : (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem physical_residual_width (I Q : Ideal O) (hI : I ≠ 0)
    (Z M O₀ H Ck CO CH : ℝ) (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hres : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ)) :
    H ≤ M - O₀ + Real.log (CH * Ck * CO) / Real.log Z := by
  have hz0 : 0 < Z := by linarith
  have hp := (div_le_iff₀ hCO).mp hpow
  have hr := (div_le_iff₀ hCH).mp hres
  have hs : Z ^ (H + O₀) ≤ (CH * Ck * CO) * Z ^ M := by
    calc
      _ = Z ^ H * Z ^ O₀ := Real.rpow_add hz0 _ _
      _ ≤ ((Ideal.absNorm (rowResidualPart I Q) : ℝ) * CH) *
          ((Ideal.absNorm (rowPowerfulPart I) : ℝ) * CO) :=
        mul_le_mul hr hp (Real.rpow_nonneg hz0.le _) (by positivity)
      _ = (CH * CO) * ((Ideal.absNorm (rowPowerfulPart I) : ℝ) *
          (Ideal.absNorm (rowResidualPart I Q) : ℝ)) := by ring
      _ ≤ (CH * CO) * (Ideal.absNorm I : ℝ) :=
        mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using actual_residual_norm_width I Q hI) (by positivity)
      _ ≤ (CH * CO) * (Ck * Z ^ M) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring
  have hl := Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz0 _) hs
  rw [Real.logb_rpow hz0 (ne_of_gt hZ), Real.logb_mul (by positivity) (by positivity),
    Real.logb_rpow hz0 (ne_of_gt hZ)] at hl
  unfold Real.logb at hl
  linarith

theorem constant_log_error (C η : ℝ) (_hC : 0 < C) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → Real.log C / Real.log Z ≤ η := by
  refine ⟨max 2 (Real.exp (Real.log C / η)), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Z hZ
  have hz : 1 < Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have he : Real.exp (Real.log C / η) ≤ Z := (le_max_right _ _).trans hZ
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  apply (div_le_iff₀ (Real.log_pos hz)).mpr
  have hh := (div_le_iff₀ hη).mp hl
  nlinarith

theorem reflectionConductorCost_pos {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (j : ι → ℕ) (e : ι → Fin 3) :
    0 < reflectionConductorCost P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost
  positivity

theorem logb_reflectionConductorCost {ι : Type*} [Fintype ι]
    (Z : ℝ) (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (j : ι → ℕ) (e : ι → Fin 3) :
    Real.logb Z (reflectionConductorCost P j e) = reflectionWidth Z P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost reflectionWidth normWidth
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (hd 1).ne' (hd 0).ne', Real.logb_pow, Real.logb_pow]
  norm_num
  ring

theorem reflection_charge_width {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z : ℝ) (hZ : 1 < Z) :
    2 * normWidth Z (rowResidualPart I (B * F * R)) +
      reflectionWidth Z P (fun i => completedLocalExponent I F (P i)) e ≤
      normWidth Z B + 2 * normWidth Z I - normWidth Z (rowPowerfulPart I) +
        normWidth Z F + normWidth Z R := by
  have hi := actual_ideal_norm_pos I hI
  have hf := actual_ideal_norm_pos F hF
  have hb := actual_ideal_norm_pos B hB
  have hr := actual_ideal_norm_pos R hR
  have hp := actual_ideal_norm_pos (rowPowerfulPart I) (rowPowerfulPart_ne_zero I)
  have hx := actual_ideal_norm_pos (rowResidualPart I (B * F * R))
    (squarefreeResidualPart_ne_zero (rowSimplePart I) (B * F * R))
  have hc := reflectionConductorCost_pos P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e
  have hh := Real.logb_le_logb_of_le hZ (mul_pos (sq_pos_of_pos hx) hc)
    (actual_common_width_charge_label_puncture I F R B hI hF hR hB P hcop hpool hres e)
  rw [Real.logb_mul (by positivity) hc.ne', Real.logb_pow,
    logb_reflectionConductorCost Z P (fun i => NeZero.ne (P i)),
    Real.logb_mul (by positivity) hr.ne', Real.logb_mul (by positivity) hf.ne',
    Real.logb_mul hb.ne' (by positivity), Real.logb_div (by positivity) hp.ne',
    Real.logb_pow] at hh
  unfold normWidth
  norm_num at hh ⊢
  linarith

theorem normWidth_upper (I : Ideal O) (hI : I ≠ 0) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : (Ideal.absNorm I : ℝ) ≤ C * Z ^ E) :
    normWidth Z I ≤ E + Real.logb Z C := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (actual_ideal_norm_pos I hI) h
  rw [Real.logb_mul hC.ne' (by positivity), Real.logb_rpow hz0 (ne_of_gt hZ)] at hh
  unfold normWidth
  linarith

theorem normWidth_lower (I : Ideal O) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : Z ^ E / C ≤ (Ideal.absNorm I : ℝ)) :
    E - Real.logb Z C ≤ normWidth Z I := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (div_pos (Real.rpow_pos_of_pos hz0 E) hC) h
  rwa [Real.logb_div (by positivity) hC.ne', Real.logb_rpow hz0 (ne_of_gt hZ)] at hh

theorem logb_widthConstant (Z : ℝ) (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH) (hf : 0 < Cf) :
    Real.logb Z (widthConstant B Ck CO CH Cf) =
      2 * Real.logb Z CH + normWidth Z B + 2 * Real.logb Z Ck +
        Real.logb Z CO + Real.logb Z Cf := by
  have hb := actual_ideal_norm_pos B hB
  unfold widthConstant normWidth
  rw [Real.logb_mul (by positivity) hf.ne', Real.logb_mul (by positivity) ho.ne',
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) hb.ne',
    Real.logb_pow, Real.logb_pow]
  norm_num

theorem terminal_common_width {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z M O₀ H V za Nstar Ck CO CH Cf : ℝ) (hZ : 1 < Z)
    (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V) :
    terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e -
      normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0) -
      normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2) ≤
        2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
          Real.log (widthConstant B Ck CO CH Cf) / Real.log Z := by
  have hb := reflection_charge_width I F B R hI hF hB hR P hcop hpool hres e Z hZ
  have h₁ := normWidth_upper I hI Z Ck M hZ hCk hk
  have h₂ := normWidth_lower (rowPowerfulPart I) Z CO O₀ hZ hCO hpow
  have h₃ := normWidth_lower (rowResidualPart I (B * F * R)) Z CH H hZ hCH hrow
  have h₄ := normWidth_upper F hF Z Cf V hZ hCf hf
  change _ ≤ 2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
    Real.logb Z (widthConstant B Ck CO CH Cf)
  rw [logb_widthConstant Z B hB Ck CO CH Cf hCk hCO hCH hCf]
  unfold terminalDualWidth reflectionWidth at *
  linarith

theorem normWidth_nonneg (Z : ℝ) (hZ : 1 < Z) (I : Ideal O) (hI : I ≠ 0) :
    0 ≤ normWidth Z I := Real.logb_nonneg hZ (norm_one_le I hI)

theorem hybridSaving_nonneg {v za : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ za) :
    0 ≤ hybridSaving v za := by unfold hybridSaving; positivity

theorem hybridSaving_half {v za : ℝ} (hv : 0 ≤ v)
    (hu : hybridSaving v za ≠ za) : v / 2 ≤ hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v + za) / 3)) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v + za) / 3) with hz | hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      linarith

theorem terminal_width_from_invariant
    {F₀ N V M Q z₀ c O₀ za Nstar hhat d η Td S₀ B₀ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hF : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hwidth : Td - S₀ - B₀ ≤ 2 * M - O₀ + Q + V - Nstar + 2 * za + η) :
    Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η := by
  have hi := hinv.1
  linarith

theorem reflected_row_bound {O₀ H S₀ B₀ za v ell el Td M η : ℝ}
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hrow : v + ell ≤ H) (hH : H ≤ M - O₀ + η) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ M + za + 5 * η / 3 := by
  have hu := hybridSaving_nonneg hv hz
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_left hrow]
  linarith

theorem reflected_column_full_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hl : 0 ≤ ell) (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za = za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) + 5 * η / 3 + τ := by
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol, hu]
  linarith

theorem reflected_column_partial_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za ≠ za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) / 2 + za + 7 * η / 6 + τ / 2 := by
  have hu' := hybridSaving_half hv hu
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol]
  linarith

theorem reflected_terminal_cases
    {F₀ M Q z₀ c O₀ H S₀ B₀ za v ell el Td d η τ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η) :
    (v + ell ≤ H → reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - c + 5 * η / 3) ∧
    (H ≤ v + ell → hybridSaving v za = za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - 2 * c + 5 * d + 17 * η / 3 + τ) ∧
    (H ≤ v + ell → hybridSaving v za ≠ za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
        F₀ - M / 4 - 3 * c / 4 + 5 * d / 2 + 19 * η / 6 + τ / 2) := by
  obtain ⟨hi₁, hi₂⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro hrow
    have hb := reflected_row_bound hO hS hB hz hv hl he hrow hH (Td := Td)
    linarith
  · intro hcol hu
    have hb := reflected_column_full_bound hl he hcol hu hret (O₀ := O₀) (S₀ := S₀) (B₀ := B₀)
    linarith
  · intro hcol hu
    have hb := reflected_column_partial_bound hS hB hv hl he hcol hu hret (O₀ := O₀)
    linarith

theorem reflected_terminal_saving
    {F₀ M Q z₀ c cstar O₀ H S₀ B₀ za v ell el Td d η τ π : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td + π ≤ F₀ - cstar / 4 := by
  obtain ⟨hr, hf, hp⟩ := reflected_terminal_cases hinv hQ hO hS hB hz hzcap hv hl he hret hH hT
  rcases le_total (v + ell) H with h | h
  · have := hr h
    linarith
  · by_cases hu : hybridSaving v za = za
    · have := hf h hu
      linarith
    · have := hp h hu
      linarith

theorem ramified_width_threshold (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ m : ℕ, -η ≤ ramifiedWidth Z m := by
  obtain ⟨Z₀, hZ₀, hlog⟩ := constant_log_error ((3 : ℝ) ^ (4 : ℕ)) η (by norm_num) hη
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ m
  have hz := hZ₀.trans_le hZ
  have hl := hlog Z hZ
  change Real.logb Z ((3 : ℝ) ^ (4 : ℕ)) ≤ η at hl
  rw [Real.logb_pow] at hl
  have hn : 0 ≤ Real.logb Z 3 := Real.logb_nonneg hz (by norm_num)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold ramifiedWidth
  norm_num at hl
  nlinarith

theorem actual_terminal_saving {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (hlogH : Real.log (CH * Ck * CO) / Real.log Z ≤ η)
    (hlogT : Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hret : v + 3 * ell + el ≤
      terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H
      (normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0))
      (normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2))
      za v ell el (terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e) + π ≤
        F₀ - cstar / 4 := by
  have hH := physical_residual_width I (B * F * R) hI Z M O₀ H Ck CO CH hZ hCk hCO hCH hk hpow hrow
  have hT := terminal_common_width I F B R hI hF hB hR P hcop hpool hres e
    Z M O₀ H V za Nstar Ck CO CH Cf hZ hCk hCO hCH hCf hk hpow hrow hf
  have hT' := terminal_width_from_invariant (O₀ := O₀) (za := za) (η := η)
    (Td := terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e)
    (S₀ := normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0))
    (B₀ := normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2))
    hinv hF₀ hscale hV hh (hT.trans (by linarith))
  exact reflected_terminal_saving hinv (normWidth_nonneg Z hZ R hR) hM hO
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 0))
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 2))
    hz hzcap hv hl he hret (by linarith) hT' hc hmargin hd hη hτ hπ

end SevenEighths.InverseTerminalWidths

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.NormalizedColumns
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma frozenExtracted_ne_zero (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) (v : Fin 3) :
    frozenExtracted F jF e v ≠ 0 := by
  apply reflectionExtractedDivisor_ne_zero
  intro i
  rw [F.generator_span]
  exact NeZero.ne _

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Extraction
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ]

lemma frozenBranchColumn_divisibility (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis)
    (hn : primaryGenerator n ≠ 0) (hb : primaryGenerator b ≠ 0)
    (hz : frozenBranchColumn F jF e A n b ≠ 0) :
    frozenExtracted F jF e 1 ∣ n ∧ frozenExtracted F jF e 2 ∣ b ∧
      ∀ i, jF i=4 → e i=2 → primaryGenerator n ∉ F.ideal i := by
  have hcp : Pairwise (fun i k => IsCoprime (Ideal.span {F.generator i}) (Ideal.span {F.generator k})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hh := reflectedBranch_divisibility (fun i => Ideal.span {F.generator i}) F.generator_good hcp
    jF e (primaryGenerator n) (primaryGenerator b) (mul_ne_zero_iff.mp hz).2
  simpa only [frozenExtracted,(primaryGenerator_spec n hn).1,(primaryGenerator_spec b hb).1,
    PrimeFamily.generator_span] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.KernelGeometry
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma PrimeFamily.product_span {ι : Type*} [Fintype ι] (G : PrimeFamily ι) :
    Ideal.span {∏ i, G.generator i} = ∏ i, G.ideal i := by
  have hf (T : Finset ι) : Ideal.span {∏ i ∈ T, G.generator i} = ∏ i ∈ T, G.ideal i := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi,Finset.prod_insert hi,← Ideal.span_singleton_mul_span_singleton,
        G.generator_span,ih]
  exact hf Finset.univ

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.KernelActual
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma fixedKernelCoefficient_pos (X tau r : ℝ) (C D1 D2 : Ideal Eis)
    (hX : 0<X) (htau : 0<tau) (hr : 0< r) (hC : C≠0) (hD1 : D1≠0) (hD2 : D2≠0) :
    0<fixedKernelCoefficient X tau r C D1 D2 := by
  have hn (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hCn := hn C hC
  have h1 := hn D1 hD1
  have h2 := hn D2 hD2
  unfold fixedKernelCoefficient
  positivity

lemma actualKernelCoefficient_pos (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c≠0) (m : ℕ) (X : ℝ) (hX : 0<X) : 0<actualKernelCoefficient F s m X := by
  apply fixedKernelCoefficient_pos _ _ _ _ _ _ hX (sourceCuspScale_pos _)
    (ramifiedScale_pos _ _ (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) _) _ one_ne_zero one_ne_zero
  apply mul_ne_zero
  · exact Ideal.span_singleton_eq_bot.not.mpr hc
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i))

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Surviving
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {a c : Eis} {mode : Bool}

lemma mem_survivingFrozenBranches (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (e : φ→Fin 3) :
    e∈survivingFrozenBranches F jF A nset bset ↔
      ∃ n∈nset, ∃ b∈bset, frozenBranchColumn F jF e A n b≠0 := by
  simp [survivingFrozenBranches]

theorem surviving_forced_norms (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (Y B : ℝ)
    (hn : ∀ n∈nset, primaryGenerator n≠0 ∧ (Ideal.absNorm n:ℝ)≤Y)
    (hb : ∀ b∈bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B)
    (e : φ→Fin 3) (he : e∈survivingFrozenBranches F jF A nset bset) :
    (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)≤Y ∧
    (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)≤B := by
  obtain ⟨n,hn',b,hb',hz⟩ := (mem_survivingFrozenBranches F jF A nset bset e).mp he
  obtain ⟨hd1,hd2,_⟩ := frozenBranchColumn_divisibility F hF jF e A n b (hn n hn').1 (hb b hb').1 hz
  have hn0 : n≠0 := by intro h; exact (hn n hn').1 (by rw [h,primaryGenerator_zero])
  have hb0 : b≠0 := by intro h; exact (hb b hb').1 (by rw [h,primaryGenerator_zero])
  have hnpos : 0<Ideal.absNorm n := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn0)
  have hbpos : 0<Ideal.absNorm b := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hb0)
  constructor
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm hd1)) (hn n hn').2
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd hbpos (map_dvd Ideal.absNorm hd2)) (hb b hb').2

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.AnnularNormalization
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

theorem annular_kernel_threshold (Z T tau C r QK QP Qn Qb kn kb D1 D2 : ℝ)
    (hT : 0<T) (htau : 0<tau) (hC : 0<C) (hr : 0< r)
    (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkn : 0<kn) (hkb : 0<kb) (h1 : 0<D1) (h2 : 0<D2) :
    Real.logb Z (kn*Qn/D1)+3*Real.logb Z (kb*Qb/D2)+3*Real.logb Z r-
      Real.logb Z (kernelCenter (T/(27*tau^2*C ^2)*r^3) QK QP Qn Qb) =
    Real.logb Z (27*tau^2*C ^2*QK^2*QP^2*kn*kb^3/(T*D1*D2^3)) := by
  have hR : 0<kernelCenter (T/(27*tau^2*C ^2)*r^3) QK QP Qn Qb := by
    unfold kernelCenter
    positivity
  have hv : 0<kn*Qn/D1 := by positivity
  have hl : 0<kb*Qb/D2 := by positivity
  have heq : (kn*Qn/D1)*(kb*Qb/D2)^3*r^3 /
      kernelCenter (T/(27*tau^2*C ^2)*r^3) QK QP Qn Qb =
      27*tau^2*C ^2*QK^2*QP^2*kn*kb^3/(T*D1*D2^3) := by
    unfold kernelCenter
    field_simp
  rw [← heq,Real.logb_div (by positivity) hR.ne',
    Real.logb_mul (by positivity) (pow_ne_zero _ hr.ne'),
    Real.logb_mul hv.ne' (pow_ne_zero _ hl.ne'),Real.logb_pow,Real.logb_pow]
  norm_num

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.RamifiedWidth
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open CompletedDyadic CompletedGauss
noncomputable section

lemma literal_ramified_log_width (Z : ℝ) (m : ℕ) :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      (m:ℝ)*Real.logb Z 3 := by
  rw [ramifiedScale,one_mul,Real.logb_pow,completedRamifiedStep,
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<3)]
  ring

lemma literal_ramified_width_offset (Z : ℝ) (m : ℕ) :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      InverseTerminalWidths.ramifiedWidth Z m + 4*Real.logb Z 3 := by
  rw [literal_ramified_log_width]
  unfold InverseTerminalWidths.ramifiedWidth
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.TerminalThreshold
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

lemma frozenExtracted_eq_ideal (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (v : Fin 3) :
    frozenExtracted F jF e v = reflectionExtractedDivisor F.ideal jF e v := by
  simp only [frozenExtracted,PrimeFamily.generator_span]

theorem actual_kernel_terminal_threshold (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (m : ℕ) (Z T QK QP Qn Qb kn kb : ℝ)
    (hT : 0<T) (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkn : 0<kn) (hkb : 0<kb) :
    Real.logb Z (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))+
      3*Real.logb Z (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2))+
      3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)-
      Real.logb Z (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb) =
    InverseTerminalWidths.terminalDualWidth Z (Real.logb Z QK) (Real.logb Z QP) (Real.logb Z T)
      F.ideal jF e +
    Real.logb Z (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3) := by
  have hr : 0< ramifiedScale 1 completedRamifiedStep m := ramifiedScale_pos _ _
    (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) _
  have htau := sourceCuspScale_pos s.index
  have hp (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hcn := hp (Ideal.span {c}) (Ideal.span_singleton_eq_bot.not.mpr hc)
  have hfn := hp (∏ i, F.ideal i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i)))
  have hd (v : Fin 3) := hp (frozenExtracted F jF e v) (frozenExtracted_ne_zero F jF e v)
  have hcc : actualKernelCoefficient F s m T =
      T/(27*(sourceCuspScale s.index)^2*
        ((Ideal.absNorm (Ideal.span {c}):ℝ)*(Ideal.absNorm (∏ i,F.ideal i):ℝ))^2)*
      (ramifiedScale 1 completedRamifiedStep m)^3 := by
    simp only [actualKernelCoefficient,fixedKernelCoefficient,map_one,Nat.cast_one,one_pow,mul_one,map_mul,Nat.cast_mul]
  rw [hcc,annular_kernel_threshold Z T (sourceCuspScale s.index)
    ((Ideal.absNorm (Ideal.span {c}):ℝ)*(Ideal.absNorm (∏ i,F.ideal i):ℝ))
    _ QK QP Qn Qb kn kb _ _ hT htau (mul_pos hcn hfn) hr hK hP hn hb hkn hkb (hd 1) (hd 2)]
  unfold InverseTerminalWidths.terminalDualWidth InverseTerminalWidths.normWidth
  rw [← frozenExtracted_eq_ideal F jF e 1,← frozenExtracted_eq_ideal F jF e 2]
  have hd1 := hd 1
  have hd2 := hd 2
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
  norm_num only [Nat.cast_ofNat]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.UpperThreshold
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

theorem actual_kernel_upper_threshold (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (m : ℕ) (Z T QK QP Qn Qb kK kP kn kb : ℝ)
    (hT : 0<T) (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) :
    Real.logb Z (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))+
      3*Real.logb Z (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2))+
      3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)-
      Real.logb Z (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb) =
    InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z T)
      F.ideal jF e +
    Real.logb Z (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)) := by
  rw [actual_kernel_terminal_threshold F jF e s hc m Z T QK QP Qn Qb kn kb hT hK hP hn hb hkn hkb]
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  unfold InverseTerminalWidths.terminalDualWidth
  rw [Real.logb_div (by positivity) (by positivity),Real.logb_mul hkK.ne' hK.ne',
    Real.logb_mul hkP.ne' hP.ne',Real.logb_mul (pow_ne_zero _ hkK.ne') (pow_ne_zero _ hkP.ne'),
    Real.logb_pow,Real.logb_pow]
  norm_num only [Nat.cast_ofNat]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.BranchCount
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedGauss
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma primeFamily_support_card (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) :
    (IdealMobiusDivisorSum.primeSupport (∏ i,F.ideal i)).card=Fintype.card φ := by
  have hc : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {F.generator i})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hh := InverseMoment.finite_primeSupport_card F.generator hc Finset.univ
  simpa only [PrimeFamily.product_span,Finset.card_univ] using hh

theorem branch_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (F : PrimeFamily ι),
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (Fintype.card (ι→Fin 3):ℝ)^2≤C*(Ideal.absNorm (∏ i,F.ideal i):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/4) (by positivity)
  refine ⟨C ^4,by positivity,?_⟩
  intro ι _ F hF
  have hI : (∏ i,F.ideal i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i))
  have hnorm : (0:ℝ)<Ideal.absNorm (∏ i,F.ideal i) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hh := hb (∏ i,F.ideal i) hI
  rw [primeFamily_support_card F hF] at hh
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  calc
    ((3:ℝ)^Fintype.card ι)^2 = (9:ℝ)^Fintype.card ι := by
      rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    _ ≤ (16:ℝ)^Fintype.card ι := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = ((2:ℝ)^Fintype.card ι)^4 := by
      rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    _ ≤ (C*(Ideal.absNorm (∏ i,F.ideal i):ℝ)^(ε/4))^4 :=
      pow_le_pow_left₀ (by positivity) hh _
    _ = C ^4*(Ideal.absNorm (∏ i,F.ideal i):ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hnorm.le]
      congr 2
      norm_num

theorem surviving_branch_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (F : PrimeFamily ι),
      Pairwise (Function.onFun IsCoprime F.ideal) →
      ∀ (jF : ι→ℕ) (A : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ)
        (nset bset : Finset (Ideal ActualEisensteinCubic.O)),
      ((survivingFrozenBranches F jF A nset bset).card:ℝ)^2≤
        C*(Ideal.absNorm (∏ i,F.ideal i):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := branch_count_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ F hF jF A nset bset
  have hcard : ((survivingFrozenBranches F jF A nset bset).card:ℝ)≤Fintype.card (ι→Fin 3) := by
    exact_mod_cast Finset.card_le_univ _
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2).trans (hb F hF)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.DyadicBox
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma ramifiedScale_one_cube (m : ℕ) : (ramifiedScale 1 completedRamifiedStep m)^3=(3:ℝ)^m := by
  have hs : completedRamifiedStep^3=(3:ℝ) := by
    unfold completedRamifiedStep
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  simp only [ramifiedScale,one_mul]
  rw [← pow_mul,Nat.mul_comm m 3,pow_mul,hs]

lemma rawDyadicCenter_pow_lower (scale : ℝ) (hs : 0≤ scale) (i : ℕ×ℕ×ℕ) :
    scale*(2:ℝ)^(i.1+i.2.2+3*i.2.1)≤ rawDyadicCenter scale i := by
  unfold rawDyadicCenter
  rw [ramifiedScale_one_cube,pow_add,pow_add,Nat.mul_comm 3 i.2.1,pow_mul]
  simp only [mul_assoc]
  have hm : (2:ℝ)^i.1≤(3:ℝ)^i.1 := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  gcongr

lemma center_mem_retainedDyadicBox (scale B : ℝ) (hs : 0<scale)
    (i : ℕ×ℕ×ℕ) (hi : rawDyadicCenter scale i≤B) : i∈retainedDyadicBox scale B := by
  let R := max 1 (B/scale)
  have hR : 1≤R := le_max_left _ _
  have hp : (2:ℝ)^(i.1+i.2.2+3*i.2.1)≤R :=
    ((le_div_iff₀ hs).mpr (by nlinarith only [rawDyadicCenter_pow_lower scale hs.le i,hi])).trans (le_max_right _ _)
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(i.1+i.2.2+3*i.2.1)) hp
  rw [Real.log_pow] at hl
  have hc : ((i.1+i.2.2+3*i.2.1:ℕ):ℝ)≤ columnDyadicLength R := by
    apply le_trans ((le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr hl)
    exact Nat.le_ceil _
  have hc' : i.1+i.2.2+3*i.2.1≤ columnDyadicLength R := by exact_mod_cast hc
  simp only [retainedDyadicBox,Finset.mem_product,Finset.mem_range]
  change i.1<columnDyadicLength R+1 ∧ i.2.1<columnDyadicLength R+1 ∧ i.2.2<columnDyadicLength R+1
  omega

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.TruncatedSource
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

lemma mem_retainedDyads (scale B : ℝ) (hs : 0<scale) (i : ℕ×ℕ×ℕ) :
    i∈retainedDyads scale B ↔ rawDyadicCenter scale i≤B := by
  simp only [retainedDyads,Finset.mem_filter]
  exact ⟨And.right,fun hi => ⟨center_mem_retainedDyadicBox scale B hs i hi,hi⟩⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.FamilyTail
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma familyRawScale_pos (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X QK QP : ℝ) (hX : 0<X) (hQK : 0<QK) (hQP : 0<QP) : 0<familyRawScale F s X QK QP :=
  div_pos (actualKernelCoefficient_pos F s hc 0 X hX) (mul_pos (sq_pos_of_pos hQK) (sq_pos_of_pos hQP))

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.PoolArithmetic
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma poolPrimeFamily_pairwise (R Q Q₀ : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (poolPrimeFamily R Q Q₀).ideal) := by
  intro P T hPT
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPT)

lemma poolPrimeFamily_fiber_divides (R I Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    (poolPrimeFamily R Q Q₀).ideal P∣I*Q :=
  FreeReflection.pool_divides I Q Q₀ hI hQ (nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask P)

lemma poolPrimeFamily_fiber_exponent (R I F Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    completedLocalExponent I F ((poolPrimeFamily R Q Q₀).ideal P)=completedLocalExponent R F P.val :=
  nonresidualPoolEquiv_exponent R I F Q Q₀ hR hI hQ hpow hmask P

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.OptionalWidth
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem original_optional_terminal_saving
    (J I F B R Q₀ : Ideal O) (hJ : J≠0) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I)
    (hmask : rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R))
    (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
    (e : A→Fin 3)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (hlogH : Real.log (CH * Ck * CO) / Real.log Z ≤ η)
    (hlogT : Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hret : v + 3 * ell + el ≤
      terminalDualWidth Z H za Nstar ((poolPrimeFamily J (B*F*R) Q₀).restrict A).ideal (fun a : A => completedLocalExponent J F a.val.val) e + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    InverseTerminalWidths.reflectedExponent 0 H
      (normWidth Z (frozenExtracted ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (fun a : A => completedLocalExponent J F a.val.val) e 0))
      (normWidth Z (frozenExtracted ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (fun a : A => completedLocalExponent J F a.val.val) e 2))
      za v ell el (terminalDualWidth Z H za Nstar ((poolPrimeFamily J (B*F*R) Q₀).restrict A).ideal (fun a : A => completedLocalExponent J F a.val.val) e) + O₀/2 + π ≤
        F₀ - cstar / 4 := by
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun a : A => completedLocalExponent J F a.val.val
  have hQ : B*F*R≠0 := mul_ne_zero (mul_ne_zero hB hF) hR
  have hj : (fun i => completedLocalExponent I F (G.ideal i))=j := by
    funext i
    exact poolPrimeFamily_fiber_exponent J I F (B*F*R) Q₀ hJ hI hQ hpower hmask i.val
  have hret' : v+3*ell+el≤terminalDualWidth Z H za Nstar G.ideal
      (fun i => completedLocalExponent I F (G.ideal i)) e+τ := by
    rw [hj]
    exact hret
  have hh := actual_terminal_saving I F B R hI hF hB hR G.ideal
    ((poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A)
    (fun a => poolPrimeFamily_fiber_divides J I (B*F*R) Q₀ hJ hI hQ hpower hmask a.val)
    (fun a => FreeReflection.pool_nonresidual I (B*F*R) Q₀
      (CanonicalRowCompletion.nonresidualPoolEquiv J I (B*F*R) Q₀ hJ hI hQ hpower hmask a.val)) e
    Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf
    hZ hCk hCO hCH hCf hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    hM hO hz hzcap hv hl he hret' hc hmargin hd hη hτ hπ
  rw [hj,← frozenExtracted_eq_ideal G j e 0,← frozenExtracted_eq_ideal G j e 2] at hh
  convert (preTransparency := .instances) hh using 1
  unfold InverseTerminalWidths.reflectedExponent
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.RetainedWidth
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u
variable {a c : Eis} {mode : Bool}

lemma family_center_eq_kernel {φ : Type u} [Fintype φ] (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (X QK QP : ℝ) (i : ℕ×ℕ×ℕ) :
    rawDyadicCenter (familyRawScale F s X QK QP) i=
      kernelCenter (actualKernelCoefficient F s i.1 X) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) := by
  unfold rawDyadicCenter familyRawScale kernelCenter actualKernelCoefficient fixedKernelCoefficient
  simp only [map_one,Nat.cast_one,one_pow,mul_one,ramifiedScale,pow_zero,one_mul]
  ring

theorem actual_retained_width_uniform
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ],
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (Z X QK QP δ : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<X → 0<QK → 0<QP →
      i∈retainedDyads (familyRawScale F s X QK QP) (16*Z^δ) →
      Real.logb Z (kn*((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))+
        3*Real.logb Z (kb*((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))+
        InverseTerminalWidths.ramifiedWidth Z i.1 ≤
      InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z X)
        F.ideal jF e + δ+η := by
  let Cf := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  have hCf : 0<Cf := by dsimp only [Cf]; positivity
  obtain ⟨Z₀,hZ₀,hlog⟩ := InverseTerminalWidths.constant_log_error (16*Cf) η (by positivity) hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro φ _ F jF e Z X QK QP δ i hZ hX hQK hQP hi
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hs := familyRawScale_pos F s hc X QK QP hX hQK hQP
  have hret := (mem_retainedDyads _ _ hs i).mp hi
  rw [family_center_eq_kernel] at hret
  have hR : 0<kernelCenter (actualKernelCoefficient F s i.1 X) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) := by
    have hcoef := actualKernelCoefficient_pos F s hc i.1 X hX
    unfold kernelCenter
    positivity
  have hrl := Real.logb_le_logb_of_le hz hR hret
  rw [Real.logb_mul (by norm_num : (16:ℝ)≠0) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hz) δ).ne',
    Real.logb_rpow (lt_trans zero_lt_one hz) (ne_of_gt hz)] at hrl
  have he := actual_kernel_upper_threshold F jF e s hc i.1 Z X QK QP
    ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) kK kP kn kb hX hQK hQP (by positivity) (by positivity) hkK hkP hkn hkb
  rw [literal_ramified_width_offset] at he
  have hl : Real.logb Z 16+Real.logb Z Cf≤η := by
    rw [←Real.logb_mul (by norm_num : (16:ℝ)≠0) hCf.ne']
    exact hlog Z hZ
  have hoff : 0≤4*Real.logb Z 3 := mul_nonneg (by norm_num) (Real.logb_nonneg hz (by norm_num))
  change _ = _+Real.logb Z Cf at he
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.ShellDomains
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma reflectedNDyad_bounds (k : ℕ) : ∀ n∈reflectedNDyad k,
    CubicSieve.Admissible n ∧ (2:ℝ)^k/2≤(Ideal.absNorm n:ℝ) ∧ (Ideal.absNorm n:ℝ)≤(2:ℝ)^k := by
  intro n hn
  exact ⟨(Finset.mem_filter.mp hn).2,(dualIdealDyad_bounds k n (Finset.mem_filter.mp hn).1).2⟩

lemma reflectedBDyad_bounds (j : ℕ) : ∀ b∈reflectedBDyad j,
    primaryGenerator b≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm b:ℝ) ∧ (Ideal.absNorm b:ℝ)≤(2:ℝ)^j := by
  intro b hb
  exact ⟨(Finset.mem_filter.mp hb).2,(dualIdealDyad_bounds j b (Finset.mem_filter.mp hb).1).2⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.SurvivingGate
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u
variable {a c : Eis} {mode : Bool}

theorem actual_surviving_retained_gates
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ],
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ→ℕ) (A : Ideal Eis→Ideal Eis→ℂ) (e : φ→Fin 3)
      (Z X QK QP δ : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<X → 0<QK → 0<QP →
      i∈retainedDyads (familyRawScale F s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches F jF A (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))
      0≤v ∧ 0≤ell ∧ -η≤InverseTerminalWidths.ramifiedWidth Z i.1 ∧
      v+3*ell+InverseTerminalWidths.ramifiedWidth Z i.1≤
        InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z X)
          F.ideal jF e+δ+η := by
  obtain ⟨Z₁,hZ₁,hwidth⟩ := actual_retained_width_uniform s hc kK kP 1 1 η hkK hkP (by norm_num) (by norm_num) hη
  obtain ⟨Z₂,hZ₂,hram⟩ := InverseTerminalWidths.ramified_width_threshold η hη
  refine ⟨max Z₁ Z₂,lt_of_lt_of_le hZ₁ (le_max_left _ _),?_⟩
  intro φ _ F hF jF A e Z X QK QP δ i hZ hX hQK hQP hi he
  have hz1 := (le_max_left Z₁ Z₂).trans hZ
  have hz2 := (le_max_right Z₁ Z₂).trans hZ
  have hz := lt_of_lt_of_le hZ₁ hz1
  have hnorm := surviving_forced_norms F hF jF A (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
    ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
    (fun n hn => ⟨(reflectedNDyad_bounds _ n hn).1.2,(reflectedNDyad_bounds _ n hn).2.2⟩)
    (fun b hb => ⟨(reflectedBDyad_bounds _ b hb).1,(reflectedBDyad_bounds _ b hb).2.2⟩) e he
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  refine ⟨Real.logb_nonneg hz ((one_le_div (hp 1)).mpr hnorm.1),
    Real.logb_nonneg hz ((one_le_div (hp 2)).mpr hnorm.2),hram Z hz2 i.1,?_⟩
  simpa only [one_mul] using hwidth F jF e Z X QK QP δ i hz1 hX hQK hQP hi
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.OriginalSaving
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_terminal_saving
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧
    ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (e : A→Fin 3)
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))
      InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
        (normWidth Z (frozenExtracted G j e 2)) za v ell (ramifiedWidth Z i.1)
        (terminalDualWidth Z H za Nstar G.ideal j e)+O₀/2+π≤F₀-cstar/4 := by
  obtain ⟨Z₀,hZ₀,hgates⟩ := actual_surviving_retained_gates s hc₀ kK kP η hkK hkP hηpos
  refine ⟨Z₀,hZ₀,?_⟩
  intro J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ
  dsimp only
  intro hret hsurv
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hG := (poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A
  obtain ⟨hv,hell,hel,hwidth⟩ := hgates G hG j column e Z X QK QP δ i hZ hX hQK hQP hret hsurv
  rw [←heH,←heza,←heN] at hwidth
  exact original_optional_terminal_saving J I F B R Q₀ hJ hI hF hB hR hpower hmask A e
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat
    (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
    (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
    (ramifiedWidth Z i.1) d η (δ+η) π Ck CO CH Cf
    (lt_of_lt_of_le hZ₀ hZ) hCk hCO hCH hCf hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    hM hO hz hzcap hv hell hel (by simpa only [add_assoc] using hwidth)
    hc hmargin hd hη hτ hπ
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.RetainedCaps
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma retained_shell_le_ratio (scale T : ℝ) (hs : 0<scale)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*T)) :
    (2:ℝ)^i.2.2≤16*T/scale ∧ (2:ℝ)^i.2.1≤16*T/scale := by
  have hh := (mem_retainedDyads _ _ hs i).mp hi
  have hl := rawDyadicCenter_pow_lower scale hs.le i
  have hp : (2:ℝ)^(i.1+i.2.2+3*i.2.1)≤16*T/scale := by
    exact (le_div_iff₀ hs).mpr (by nlinarith)
  constructor
  · exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show i.2.2 ≤ i.1 + i.2.2 + 3 * i.2.1 by omega)).trans hp
  · exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show i.2.1 ≤ i.1 + i.2.2 + 3 * i.2.1 by omega)).trans hp

lemma retained_shell_log_cap (scale Z δ Lcap η : ℝ) (hs : 0<scale) (hZ : 1<Z)
    (hscale : scale⁻¹≤Z^Lcap) (hconst : Real.logb Z 16≤η)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*Z^δ)) :
    Real.logb Z ((2:ℝ)^i.2.2)≤δ+Lcap+η ∧
    Real.logb Z ((2:ℝ)^i.2.1)≤δ+Lcap+η := by
  have hz := lt_trans zero_lt_one hZ
  have hb : 16*Z^δ/scale≤16*Z^(δ+Lcap) := by
    rw [Real.rpow_add hz,div_eq_mul_inv,←mul_assoc]
    exact mul_le_mul_of_nonneg_left hscale (by positivity)
  have hshell := retained_shell_le_ratio scale (Z^δ) hs i hi
  have hlog (n : ℕ) (hn : (2:ℝ)^n≤16*Z^(δ+Lcap)) :
      Real.logb Z ((2:ℝ)^n)≤δ+Lcap+η := by
    have hh := Real.logb_le_logb_of_le hZ (by positivity : (0:ℝ)<2^n) hn
    rw [Real.logb_mul (by norm_num : (16:ℝ)≠0) (Real.rpow_pos_of_pos hz _).ne',
      Real.logb_rpow hz (ne_of_gt hZ)] at hh
    linarith
  exact ⟨hlog _ (hshell.1.trans hb),hlog _ (hshell.2.trans hb)⟩

lemma extracted_log_le_shell (Z Q : ℝ) (hZ : 1<Z) (hQ : 0<Q)
    (I : Ideal ActualEisensteinCubic.O) (hI : I≠0) :
    Real.logb Z (Q/Ideal.absNorm I)≤Real.logb Z Q := by
  have hn : (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply Real.logb_le_logb_of_le hZ (div_pos hQ (lt_of_lt_of_le zero_lt_one hn))
  exact div_le_self hQ.le hn

lemma retained_extracted_log_budget (scale Z δ Lscale Lrow Lslot η X L : ℝ)
    (hs : 0<scale) (hZ : 1<Z) (hX : 0<X) (hL : 0<L)
    (hscale : scale⁻¹≤Z^Lscale) (hconst : Real.logb Z 16≤η)
    (hrow : X≤Z^Lrow) (hslot : L≤Z^Lslot)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*Z^δ))
    (D1 D2 : Ideal ActualEisensteinCubic.O) (h1 : D1≠0) (h2 : D2≠0) :
    Real.logb Z X+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm D1)+
      Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm D2)+Real.logb Z L≤
        Lrow+Lslot+2*(δ+Lscale+η) := by
  have hz := lt_trans zero_lt_one hZ
  have hr := Real.logb_le_logb_of_le hZ hX hrow
  have hl := Real.logb_le_logb_of_le hZ hL hslot
  rw [Real.logb_rpow hz (ne_of_gt hZ)] at hr hl
  obtain ⟨hn,hb⟩ := retained_shell_log_cap scale Z δ Lscale η hs hZ hscale hconst i hi
  have hn' := extracted_log_le_shell Z ((2:ℝ)^i.2.2) hZ (by positivity) D1 h1
  have hb' := extracted_log_le_shell Z ((2:ℝ)^i.2.1) hZ (by positivity) D2 h2
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.OriginalExponent
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_energy_exponent
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧
    ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (e : A→Fin 3)
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))
      InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
        (normWidth Z (frozenExtracted G j e 2)) za v ell (ramifiedWidth Z i.1)
        (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+v+ell+za)+η/2+O₀/2≤F₀-cstar/4 := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_terminal_saving s hc₀ kK kP η hkK hkP hηpos
  refine ⟨Z₀,hZ₀,?_⟩
  intro J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret hsurv
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hs := hsave J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hret hsurv
  have hb := retained_extracted_log_budget (familyRawScale G s X QK QP) Z δ Lscale Lrow Lslot η
    (kK*QK) (kP*QP) (familyRawScale_pos G s hc₀ X QK QP hX hQK hQP)
    (lt_of_lt_of_le hZ₀ hZ) (mul_pos hkK hQK) (mul_pos hkP hQP) hscap hconst hrowcap hslotcap i hret
    (frozenExtracted G j e 1) (frozenExtracted G j e 2)
    (frozenExtracted_ne_zero G j e 1) (frozenExtracted_ne_zero G j e 2)
  rw [←heH,←heza] at hb
  have he := mul_le_mul_of_nonneg_left hb hε
  dsimp only [G,j] at hs hb he
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.OriginalBranchSum
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_energy_sum_oai
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (ρ : ℝ) (hρ : 0<ρ) (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ C : ℝ, 1<Z₀ ∧ 0<C ∧
    ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤ margin → d≤ cstar/200 →
      η≤ cstar/1000 → δ+η≤ cstar/1000 → π≤ cstar/1000 →
      0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      ((branches.card:ℝ)*∑ e∈branches,
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))≤
        C*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_energy_exponent s hc₀ kK kP η hkK hkP hηpos
  obtain ⟨C,hC,hcount⟩ := surviving_branch_count_small_power ρ hρ
  refine ⟨Z₀,C,hZ₀,hC,?_⟩
  intro J I F B R Q₀ hJ hI hF hB hR hpower hmask A column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hcbr := hcount G ((poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise
    (poolPrimeFamily_pairwise J (B*F*R) Q₀) A) j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hb (e : A→Fin 3) (he : e∈branches) := hsave J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε hrowcap hslotcap hconst hbudget hscap hret he
  calc
    _ ≤ (branches.card:ℝ)*∑ _e∈branches,Z^(F₀-cstar/4-O₀/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he
      apply Real.rpow_le_rpow_of_exponent_le hz'.le
      have hh := hb e he
      dsimp only at hh
      linarith
    _ = ((branches.card:ℝ)^2)*Z^(F₀-cstar/4-O₀/2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcbr (Real.rpow_nonneg (lt_trans zero_lt_one hz').le _)
end
end SevenEighths.InverseReflectedPhase

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseReflectedPhase.original_surviving_energy_sum_oai := @OAI.SevenEighths.InverseReflectedPhase.original_surviving_energy_sum_oai
