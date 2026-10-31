-- Prove2me | solution 1 for OAI.Ostmann.quadratic_gcd_corrections_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:49:57.619878+00:00
-- url     : https://prove2.me/submissions/143b0e46-653c-4fe4-ae22-25f6e80b1c42

import Mathlib
import Definitions.Def_OAIQ095D003
import Definitions.Def_OAIQ095D005
import Theorems.Thm_OAI_Ostmann_quadratic_first_total_growth

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelEigenvalueBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Schur's eigenvalue bound for the concrete finite kernel identity -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
 theorem complex_self_quadratic (u : ι → ℂ) :
    star u ⬝ᵥ u = ((∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [Complex.star_def] using Complex.conj_mul' (u s)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteMatrixDuality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Hilbert-space duality for the large-sieve phase matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

 theorem finite_complex_cauchy_schwarz {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  let U : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let V : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm v
  have hi : inner ℂ U V = star u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hh := pow_le_pow_left₀ (norm_nonneg (inner ℂ U V)) (norm_inner_le_norm U V) 2
  rw [hi, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hh
  exact hh

 theorem finite_matrix_duality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Matrix ι κ ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hdual : ∀ b : ι → ℂ, (∑ j, ‖(Fᴴ *ᵥ b) j‖ ^ 2) ≤ K * ∑ i, ‖b i‖ ^ 2)
    (c : κ → ℂ) :
    (∑ i, ‖(F *ᵥ c) i‖ ^ 2) ≤ K * ∑ j, ‖c j‖ ^ 2 := by
  let b := F *ᵥ c
  have hE : 0 ≤ ∑ i, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hC : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  by_cases hzero : (∑ i, ‖b i‖ ^ 2) = 0
  · change (∑ i, ‖b i‖ ^ 2) ≤ _
    rw [hzero]
    exact mul_nonneg hK hC
  have hEpos : 0 < ∑ i, ‖b i‖ ^ 2 := lt_of_le_of_ne hE (Ne.symm hzero)
  have hid : star (Fᴴ *ᵥ b) ⬝ᵥ c = star b ⬝ᵥ b := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hcauchy := finite_complex_cauchy_schwarz (Fᴴ *ᵥ b) c
  rw [hid, complex_self_quadratic, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hE] at hcauchy
  have hmul := mul_le_mul_of_nonneg_right (hdual b) hC
  change (∑ i, ‖b i‖ ^ 2) ≤ _
  have hh : (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) ≤
      (K * ∑ j, ‖c j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by nlinarith
  exact (mul_le_mul_iff_left₀ hEpos).mp hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeMask
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Möbius expansion of the common-divisor mask -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using h

 theorem coprime_mask_moebius (q n : ℕ) (hq : q ≠ 0) :
    (if n.Coprime q then (1 : ℤ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ n then ArithmeticFunction.moebius d else 0 := by
  have hg : n.gcd q ≠ 0 := Nat.gcd_ne_zero_right hq
  have hf : q.divisors.filter (fun d => d ∣ n) = (n.gcd q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdq, _⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdq, hg⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right n q), hq⟩,
        hd.trans (Nat.gcd_dvd_left n q)⟩
  rw [← Finset.sum_filter, hf, quadratic_moebius_divisor_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveTranspose
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity supplies the transpose needed for quadratic kernels -/

namespace Ostmann

open scoped BigOperators Classical

theorem quadraticSieveEnergy_reciprocityTwist (N : ℕ) (b : ℕ → ℂ) :
    quadraticSieveEnergy N (reciprocityTwist b) = quadraticSieveEnergy N b := by
  apply Finset.sum_congr rfl
  intro s _
  unfold reciprocityTwist
  split_ifs <;> simp

theorem quadraticTransposeSum_one_mod_four (N : ℕ) (b : ℕ → ℂ) (u : ℕ)
    (hu : u % 4 = 1) : quadraticTransposeSum N b u = quadraticSieveSum N b u := by
  apply Finset.sum_congr rfl
  intro s hs
  have hsodd := (Finset.mem_filter.mp hs).2.1
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hu hsodd]

theorem quadraticTransposeSum_three_mod_four (N : ℕ) (b : ℕ → ℂ) (u : ℕ)
    (hu : u % 4 = 3) :
    quadraticTransposeSum N b u = quadraticSieveSum N (reciprocityTwist b) u := by
  apply Finset.sum_congr rfl
  intro s hs
  have hsodd := (Finset.mem_filter.mp hs).2.1
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hsodd) with hs1 | hs3
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hs1]
    simp [reciprocityTwist, hs1]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four hu hs3]
    simp [reciprocityTwist, hs3]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveFinite
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite quadratic-sieve bounds and their reciprocity symmetry

These are the elementary initial steps of Heath-Brown (1995), sections 2--3.
The bound predicate refers to the actual Jacobi matrix and finite coefficients.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

 theorem quadraticTranspose_of_bound {M N : ℕ} {K : ℝ}
    (h : QuadraticSieveBound M N K) (b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b m‖ ^ 2) ≤
      2 * K * quadraticSieveEnergy N b := by
  have h1 := h b
  have h3 := h (reciprocityTwist b)
  rw [quadraticSieveEnergy_reciprocityTwist] at h3
  have ht : (∑ u ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b u‖ ^ 2) ≤
      (∑ u ∈ oddSquarefreeRange M, ‖quadraticSieveSum N b u‖ ^ 2) +
      ∑ u ∈ oddSquarefreeRange M, ‖quadraticSieveSum N (reciprocityTwist b) u‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    have huodd := (Finset.mem_filter.mp hu).2.1
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp huodd) with hu1 | hu3
    · rw [quadraticTransposeSum_one_mod_four N b u hu1]
      linarith [sq_nonneg ‖quadraticSieveSum N (reciprocityTwist b) u‖]
    · rw [quadraticTransposeSum_three_mod_four N b u hu3]
      linarith [sq_nonneg ‖quadraticSieveSum N b u‖]
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveMonotone
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and monotonicity for the actual quadratic-sieve matrix -/

namespace Ostmann

open scoped BigOperators Classical

 theorem oddSquarefreeRange_mono {N R : ℕ} (h : N ≤ R) :
    oddSquarefreeRange N ⊆ oddSquarefreeRange R := by
  intro n hn
  obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hrange).1, (Finset.mem_Icc.mp hrange).2.trans h⟩, hodd, hsq⟩

 theorem QuadraticSieveBound.mono_constant {M N : ℕ} {K L : ℝ}
    (h : QuadraticSieveBound M N K) (hKL : K ≤ L) : QuadraticSieveBound M N L := by
  intro b
  exact (h b).trans (mul_le_mul_of_nonneg_right hKL
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

 theorem quadraticSieveSum_restrict {N R : ℕ} (hNR : N ≤ R) (b : ℕ → ℂ) (m : ℕ) :
    quadraticSieveSum R (fun n => if n ∈ oddSquarefreeRange N then b n else 0) m =
      quadraticSieveSum N b m := by
  have hs := Finset.sum_subset (oddSquarefreeRange_mono hNR)
    (f := fun n => (if n ∈ oddSquarefreeRange N then b n else 0) * (jacobiSym (n : ℤ) m : ℂ))
    (by intro n _ hn; simp [hn])
  simpa only [Finset.sum_ite_mem, ite_mul, zero_mul, Finset.inter_self, quadraticSieveSum] using hs.symm

 theorem quadraticSieveEnergy_restrict {N R : ℕ} (hNR : N ≤ R) (b : ℕ → ℂ) :
    quadraticSieveEnergy R (fun n => if n ∈ oddSquarefreeRange N then b n else 0) =
      quadraticSieveEnergy N b := by
  have hs := Finset.sum_subset (oddSquarefreeRange_mono hNR)
    (f := fun n => ‖(if n ∈ oddSquarefreeRange N then b n else 0)‖ ^ 2)
    (by intro n _ hn; simp [hn])
  simpa only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_ite_mem, Finset.inter_self, quadraticSieveEnergy] using hs.symm

 theorem QuadraticSieveBound.mono_second {M N R : ℕ} {K : ℝ}
    (hNR : N ≤ R) (h : QuadraticSieveBound M R K) : QuadraticSieveBound M N K := by
  intro b
  have hh := h (fun n => if n ∈ oddSquarefreeRange N then b n else 0)
  simpa only [quadraticSieveSum_restrict hNR, quadraticSieveEnergy_restrict hNR] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveDivisibility
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a fixed divisor from the actual quadratic coefficient array -/

namespace Ostmann

open scoped Classical BigOperators

 theorem mem_oddSquarefreeRange_mul {s r N : ℕ} (hs : Squarefree s) (ho : Odd s) :
    s * r ∈ oddSquarefreeRange N ↔
      r ∈ oddSquarefreeRange (N / s) ∧ s.Coprime r := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs.ne_zero
  constructor
  · intro h
    obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp h
    obtain ⟨hcop, _, hrsq⟩ := Nat.squarefree_mul_iff.mp hsq
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hrsq.ne_zero,
      (Nat.le_div_iff_mul_le hs0).mpr ?_⟩, hodd.of_dvd_nat (dvd_mul_left r s), hrsq⟩, hcop⟩
    simpa only [Nat.mul_comm] using (Finset.mem_Icc.mp hrange).2
  · rintro ⟨hr, hcop⟩
    obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hs0 (Finset.mem_Icc.mp hrange).1, ?_⟩,
      ho.mul hodd, (Nat.squarefree_mul hcop).mpr ⟨hs, hsq⟩⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hs0).mp (Finset.mem_Icc.mp hrange).2

 theorem sum_oddSquarefree_multiples {R : Type*} [AddCommMonoid R]
    (s N : ℕ) (hs : Squarefree s) (ho : Odd s) (f : ℕ → R) :
    (∑ n ∈ (oddSquarefreeRange N).filter (fun n => s ∣ n), f n) =
      ∑ r ∈ (oddSquarefreeRange (N / s)).filter (fun r => s.Coprime r), f (s * r) := by
  symm
  apply Finset.sum_bij (fun r _ => s * r)
  · intro r hr
    exact Finset.mem_filter.mpr
      ⟨(mem_oddSquarefreeRange_mul hs ho).mpr (Finset.mem_filter.mp hr), dvd_mul_right s r⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hs.ne_zero) hab
  · intro n hn
    obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hn
    have he : s * (n / s) = n := Nat.mul_div_cancel' hd
    refine ⟨n / s, ?_, he⟩
    apply Finset.mem_filter.mpr
    exact (mem_oddSquarefreeRange_mul hs ho).mp (he.symm ▸ hn)
  · intro _ _
    rfl

 theorem quadraticTransposeSum_divisibility (s N : ℕ) (hs : Squarefree s) (ho : Odd s)
    (b : ℕ → ℂ) (m : ℤ) :
    quadraticTransposeSum N (fun n => if s ∣ n then b n else 0) m =
      (jacobiSym m s : ℂ) * quadraticTransposeSum (N / s) (quadraticDivisibilityCoeff s b) m := by
  unfold quadraticTransposeSum
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter, sum_oddSquarefree_multiples s N hs ho]
  simp only [quadraticDivisibilityCoeff, ite_mul, zero_mul, ← Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2.ne_zero
  rw [jacobiSym.mul_right' m hs.ne_zero hr0]
  push_cast
  ring

 theorem quadraticSieveEnergy_divisibility (s N : ℕ) (hs : Squarefree s) (ho : Odd s)
    (b : ℕ → ℂ) :
    quadraticSieveEnergy (N / s) (quadraticDivisibilityCoeff s b) =
      quadraticSieveEnergy N (fun n => if s ∣ n then b n else 0) := by
  unfold quadraticSieveEnergy quadraticDivisibilityCoeff
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ← Finset.sum_filter]
  exact (sum_oddSquarefree_multiples s N hs ho (fun n => ‖b n‖ ^ 2)).symm

 theorem quadratic_divisibility_energy {s M N : ℕ} {K : ℝ}
    (hs : Squarefree s) (ho : Odd s) (h : QuadraticSieveBound M (N / s) K)
    (b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticTransposeSum N (fun n => if s ∣ n then b n else 0) m‖ ^ 2) ≤
      2 * K * quadraticSieveEnergy N (fun n => if s ∣ n then b n else 0) := by
  have hb := quadraticTranspose_of_bound h (quadraticDivisibilityCoeff s b)
  rw [quadraticSieveEnergy_divisibility s N hs ho] at hb
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro m _
  rw [quadraticTransposeSum_divisibility s N hs ho, norm_mul, mul_pow]
  rcases jacobiSym.trichotomy (m : ℤ) s with hm | hm | hm <;> simp [hm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Möbius expansion of the coprime quadratic bilinear form -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem coprime_mask_truncated (n₁ n₂ N : ℕ) (hn₂ : 0 < n₂) (hN : n₂ ≤ N) :
    (if n₁.Coprime n₂ then (1 : ℂ) else 0) =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ n₁ then 1 else 0) * (if d ∣ n₂ then 1 else 0) := by
  have hc := congrArg (Int.cast : ℤ → ℂ) (coprime_mask_moebius n₂ n₁ hn₂.ne')
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sum] at hc
  rw [hc]
  have hsub : n₂.divisors ⊆ Finset.Icc 1 N := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      (Nat.le_of_dvd hn₂ (Nat.dvd_of_mem_divisors hd)).trans hN⟩
  have hh := Finset.sum_subset hsub
    (f := fun d => (ArithmeticFunction.moebius d : ℂ) *
      (if d ∣ n₁ then 1 else 0) * (if d ∣ n₂ then 1 else 0)) (by
        intro d _ hd
        have hd₂ : ¬d ∣ n₂ := fun h => hd (Nat.mem_divisors.mpr ⟨h, hn₂.ne'⟩)
        simp [hd₂])
  rw [← hh]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Nat.dvd_of_mem_divisors hd, ite_true, if_true, mul_one]
  split_ifs <;> simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor loss in the quadratic-sieve iteration -/

namespace Ostmann

 theorem quadratic_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hek : 1 < ε * k := by
    have hh := (div_lt_iff₀ hε).mp hk
    simpa only [mul_comm] using hh
  have hk0 : k ≠ 0 := by
    intro hz
    simp only [hz, Nat.cast_zero, mul_zero] at hek
    linarith
  obtain ⟨D, hD, hb⟩ := exists_divisors_power_bound k
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  refine ⟨D, by positivity, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hnp : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hnb : (n : ℝ) ≤ (n : ℝ) ^ (ε * k) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hek.le
  have hDp : (D : ℝ) ≤ (D : ℝ) ^ k := le_self_pow₀ hD1 hk0
  have hh : (n.divisors.card : ℝ) ^ k ≤ ((D : ℝ) * (n : ℝ) ^ ε) ^ k := by
    calc
      _ ≤ (D : ℝ) * n := by exact_mod_cast hb n hn
      _ ≤ (D : ℝ) ^ k * (n : ℝ) ^ (ε * k) :=
        mul_le_mul hDp hnb (by positivity) (by positivity)
      _ = _ := by rw [mul_pow, Real.rpow_mul hnp.le, Real.rpow_natCast]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) hk0).mp hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBilinearExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-array coprime expansion needed for divisor restrictions -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadratic_coprime_bilinear_expansion (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (m : ℤ) :
    quadraticCoprimeBilinear N₁ N₂ a b m =
      ∑ d ∈ Finset.Icc 1 N₂, (ArithmeticFunction.moebius d : ℂ) *
        quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m *
        conj (quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m) := by
  have hp (n₁ n₂ : ℕ) (hn₂ : n₂ ∈ oddSquarefreeRange N₂) :
      (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
        a n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) =
      ∑ d ∈ Finset.Icc 1 N₂, (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
    have hr := (Finset.mem_filter.mp hn₂).1
    rw [coprime_mask_truncated n₁ n₂ N₂ (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h₁ : d ∣ n₁ <;> by_cases h₂ : d ∣ n₂ <;>
      simp [h₁, h₂, mul_left_comm, mul_comm]
  unfold quadraticCoprimeBilinear
  calc
    _ = ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ n₂ ∈ oddSquarefreeRange N₂,
        ∑ d ∈ Finset.Icc 1 N₂, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
          (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
      apply Finset.sum_congr rfl
      intro n₁ _
      exact Finset.sum_congr rfl (fun n₂ hn₂ => hp n₁ n₂ hn₂)
    _ = ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ d ∈ Finset.Icc 1 N₂,
        ∑ n₂ ∈ oddSquarefreeRange N₂, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
          (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ d ∈ Finset.Icc 1 N₂, ∑ n₁ ∈ oddSquarefreeRange N₁,
        ∑ n₂ ∈ oddSquarefreeRange N₂, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
          (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [quadraticTransposeSum, map_sum, map_mul, map_intCast,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n₁ _
      apply Finset.sum_congr rfl
      intro n₂ _
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBilinearBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cauchy bounds for two independently truncated coprime arrays -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadratic_divisibility_partial_energy (D N : ℕ) (b : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 D, quadraticSieveEnergy N (fun n => if d ∣ n then b n else 0)) ≤
      ∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) * ‖b n‖ ^ 2 := by
  unfold quadraticSieveEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 := (Finset.mem_filter.mp hn).2.2.ne_zero
  have hsub : (Finset.Icc 1 D).filter (fun d => d ∣ n) ⊆ n.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hn0⟩
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (sq_nonneg _)

 theorem quadratic_coprime_bilinear_pointwise (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (m : ℤ) :
    ‖quadraticCoprimeBilinear N₁ N₂ a b m‖ ≤
      ∑ d ∈ Finset.Icc 1 N₂,
        ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ *
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ := by
  rw [quadratic_coprime_bilinear_expansion]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  have hd : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  simp only [norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ *
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ := by
      gcongr
    _ = _ := by ring

 theorem quadratic_coprime_bilinear_cauchy (M N₁ N₂ : ℕ) (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂ a b m‖) ≤
      Real.sqrt (∑ d ∈ Finset.Icc 1 N₂, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ ^ 2) *
      Real.sqrt (∑ d ∈ Finset.Icc 1 N₂, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ ^ 2) := by
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ d ∈ Finset.Icc 1 N₂,
        ‖quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m‖ *
        ‖quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m‖ :=
      Finset.sum_le_sum (fun m _ => quadratic_coprime_bilinear_pointwise N₁ N₂ a b m)
    _ = ∑ z ∈ (Finset.Icc 1 N₂).product (oddSquarefreeRange M),
        ‖quadraticTransposeSum N₁ (fun n => if z.1 ∣ n then a n else 0) z.2‖ *
        ‖quadraticTransposeSum N₂ (fun n => if z.1 ∣ n then b n else 0) z.2‖ := by
      rw [Finset.sum_comm, Finset.product_eq_sprod, Finset.sum_product]
    _ ≤ _ := by
      have hc := Real.sum_mul_le_sqrt_mul_sqrt
        ((Finset.Icc 1 N₂).product (oddSquarefreeRange M))
        (fun z => ‖quadraticTransposeSum N₁ (fun n => if z.1 ∣ n then a n else 0) z.2‖)
        (fun z => ‖quadraticTransposeSum N₂ (fun n => if z.1 ∣ n then b n else 0) z.2‖)
      simpa only [Finset.product_eq_sprod, Finset.sum_product] using hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact split of a product divisor between coprime coefficients -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadratic_divisor_split_unique {d n₁ n₂ e : ℕ} (_hd : d ≠ 0)
    (hcop : n₁.Coprime n₂) (he : e ∣ d) (h₁ : e ∣ n₁) (h₂ : d / e ∣ n₂) :
    e = d.gcd n₁ := by
  have hcross : (d / e).Coprime n₁ := hcop.symm.of_dvd_left h₂
  have hg := Nat.gcd_mul_of_coprime_of_dvd hcross h₁
  simpa only [Nat.div_mul_cancel he] using hg.symm

 theorem quadratic_divisor_split_exists {d n₁ n₂ : ℕ} (hd : 0 < d)
    (hcop : n₁.Coprime n₂) (hdiv : d ∣ n₁ * n₂) :
    d.gcd n₁ ∈ d.divisors ∧ d.gcd n₁ ∣ n₁ ∧ d / d.gcd n₁ ∣ n₂ := by
  have hprod : d.gcd n₁ * d.gcd n₂ = d :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr hdiv
  have hg : 0 < d.gcd n₁ := Nat.gcd_pos_of_pos_left n₁ hd
  have heq : d / d.gcd n₁ = d.gcd n₂ := by
    exact Nat.div_eq_of_eq_mul_left hg (by simpa only [Nat.mul_comm] using hprod.symm)
  exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hd.ne'⟩,
    Nat.gcd_dvd_right _ _, heq ▸ Nat.gcd_dvd_right d n₂⟩

 theorem quadratic_product_divisor_indicator {d n₁ n₂ : ℕ} (hd : 0 < d)
    (hcop : n₁.Coprime n₂) :
    (if d ∣ n₁ * n₂ then (1 : ℂ) else 0) =
      ∑ e ∈ d.divisors, if e ∣ n₁ ∧ d / e ∣ n₂ then (1 : ℂ) else 0 := by
  by_cases hdiv : d ∣ n₁ * n₂
  · obtain ⟨he, h₁, h₂⟩ := quadratic_divisor_split_exists hd hcop hdiv
    rw [ite_eq_left hdiv, Finset.sum_eq_single (d.gcd n₁)]
    · rw [ite_eq_left ⟨h₁, h₂⟩]
    · intro e he' hne
      apply ite_eq_right
      intro hh
      exact hne (quadratic_divisor_split_unique hd.ne' hcop
        (Nat.dvd_of_mem_divisors he') hh.1 hh.2)
    · exact fun hn => (hn he).elim
  · rw [ite_eq_right hdiv]
    symm
    apply Finset.sum_eq_zero
    intro e he
    apply ite_eq_right
    intro hh
    have hp := Nat.mul_dvd_mul hh.1 hh.2
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)] at hp
    exact hdiv hp

 theorem quadratic_divisor_bilinear_split (N₁ N₂ d : ℕ) (hd : 0 < d)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticDivisorBilinear N₁ N₂ d a b m =
      ∑ e ∈ d.divisors, quadraticCoprimeBilinear N₁ N₂
        (fun n => if e ∣ n then a n else 0)
        (fun n => if d / e ∣ n then b n else 0) m := by
  have hp (n₁ n₂ : ℕ) :
      (if n₁.Coprime n₂ ∧ d ∣ n₁ * n₂ then (1 : ℂ) else 0) *
        a n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) =
      ∑ e ∈ d.divisors, (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
        (if e ∣ n₁ then a n₁ else 0) * conj (if d / e ∣ n₂ then b n₂ else 0) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
    by_cases hc : n₁.Coprime n₂
    · simp_rw [ite_eq_left hc, one_mul]
      have hi : (if n₁.Coprime n₂ ∧ d ∣ n₁ * n₂ then (1 : ℂ) else 0) =
          (if d ∣ n₁ * n₂ then 1 else 0) := by
        by_cases hx : d ∣ n₁ * n₂ <;> simp [hc, hx]
      rw [hi, quadratic_product_divisor_indicator hd hc]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      by_cases h₁ : e ∣ n₁ <;> by_cases h₂ : d / e ∣ n₂ <;> simp [h₁, h₂]
    · simp [hc]
  unfold quadraticDivisorBilinear
  simp_rw [hp]
  calc
    _ = ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ e ∈ d.divisors,
        ∑ n₂ ∈ oddSquarefreeRange N₂,
          (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
            (if e ∣ n₁ then a n₁ else 0) * conj (if d / e ∣ n₂ then b n₂ else 0) *
            (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRestrictedBilinear
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Divisor restrictions shorten each side of the coprime bilinear form

The Möbius divisor is kept separate from the fixed divisor. No replacement
of two divisibility conditions by their product is needed.
-/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_restricted_transpose_energy {M N s D : ℕ} {K : ℝ}
    (hs : Squarefree s) (ho : Odd s) (hK : 0 ≤ K)
    (h : QuadraticSieveBound M (N / s) K) (a : ℕ → ℂ) :
    (∑ u ∈ Finset.Icc 1 D, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticTransposeSum N
        (fun n => if u ∣ n then (if s ∣ n then a n else 0) else 0) m‖ ^ 2) ≤
      2 * K * ∑ n ∈ oddSquarefreeRange N,
        (n.divisors.card : ℝ) * ‖if s ∣ n then a n else 0‖ ^ 2 := by
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 D,
        2 * K * quadraticSieveEnergy N
          (fun n => if u ∣ n then (if s ∣ n then a n else 0) else 0) := by
      apply Finset.sum_le_sum
      intro u _
      have heq : (fun n => if u ∣ n then (if s ∣ n then a n else 0) else 0) =
          (fun n => if s ∣ n then (if u ∣ n then a n else 0) else 0) := by
        funext n
        by_cases hu : u ∣ n <;> by_cases hs' : s ∣ n <;> simp [hu, hs']
      rw [heq]
      exact quadratic_divisibility_energy hs ho h _
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (quadratic_divisibility_partial_energy D N (fun n => if s ∣ n then a n else 0))
        (by positivity)

 theorem quadratic_coprime_restricted_bound {M N₁ N₂ s₁ s₂ : ℕ} {K₁ K₂ : ℝ}
    (hs₁ : Squarefree s₁) (ho₁ : Odd s₁) (hs₂ : Squarefree s₂) (ho₂ : Odd s₂)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (N₁ / s₁) K₁)
    (h₂ : QuadraticSieveBound M (N₂ / s₂) K₂) (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * ∑ n ∈ oddSquarefreeRange N₁,
        (n.divisors.card : ℝ) * ‖if s₁ ∣ n then a n else 0‖ ^ 2) *
      Real.sqrt (2 * K₂ * ∑ n ∈ oddSquarefreeRange N₂,
        (n.divisors.card : ℝ) * ‖if s₂ ∣ n then b n else 0‖ ^ 2) := by
  apply (quadratic_coprime_bilinear_cauchy M N₁ N₂ _ _).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (quadratic_restricted_transpose_energy hs₁ ho₁ hK₁ h₁ a))
    (Real.sqrt_le_sqrt (quadratic_restricted_transpose_energy hs₂ ho₂ hK₂ h₂ b))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the two divisor ranges in Heath-Brown's bilinear comparison -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticDivisorWeight_nonneg (N s : ℕ) (a : ℕ → ℂ) :
    0 ≤ quadraticDivisorWeight N s a := by
  apply Finset.sum_nonneg
  intro n _
  positivity

 theorem quadraticDivisorMoment_nonneg (N : ℕ) (a : ℕ → ℂ) :
    0 ≤ quadraticDivisorMoment N a := by
  apply Finset.sum_nonneg
  intro n _
  positivity

 theorem quadratic_divisor_weight_sum (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ s ∈ S, quadraticDivisorWeight N s a) ≤ quadraticDivisorMoment N a := by
  unfold quadraticDivisorWeight quadraticDivisorMoment
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 := (Finset.mem_filter.mp hn).2.2.ne_zero
  have hsub : S.filter (fun s => s ∣ n) ⊆ n.divisors := by
    intro s hs
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hs).2, hn0⟩
  have hc : ((S.filter (fun s => s ∣ n)).card : ℝ) ≤ n.divisors.card := by
    exact_mod_cast Finset.card_le_card hsub
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) * ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

 theorem quadratic_divisor_weight_sqrt_sum (N : ℕ) (S : Finset ℕ)
    (K : ℝ) (hK : 0 ≤ K) (a : ℕ → ℂ) :
    (∑ s ∈ S, Real.sqrt (2 * K * quadraticDivisorWeight N s a)) ≤
      Real.sqrt (2 * K * S.card * quadraticDivisorMoment N a) := by
  have hw (s : ℕ) : 0 ≤ 2 * K * quadraticDivisorWeight N s a :=
    mul_nonneg (by positivity) (quadraticDivisorWeight_nonneg N s a)
  have hc := Real.sum_mul_le_sqrt_mul_sqrt S (fun _ => (1 : ℝ))
    (fun s => Real.sqrt (2 * K * quadraticDivisorWeight N s a))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have he : (∑ s ∈ S, Real.sqrt (2 * K * quadraticDivisorWeight N s a) ^ 2) =
      2 * K * ∑ s ∈ S, quadraticDivisorWeight N s a := by
    simp only [Real.sq_sqrt (hw _), Finset.mul_sum]
  rw [he, ← Real.sqrt_mul (Nat.cast_nonneg S.card)] at hc
  apply hc.trans
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ (S.card : ℝ) * (2 * K * quadraticDivisorMoment N a) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (quadratic_divisor_weight_sum N S a) (by positivity))
        (Nat.cast_nonneg _)
    _ = _ := by ring

 theorem quadratic_divisor_family_bound (M N₁ N₂ : ℕ) (S₁ S₂ : Finset ℕ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hs₁ : ∀ s ∈ S₁, Squarefree s ∧ Odd s)
    (hs₂ : ∀ s ∈ S₂, Squarefree s ∧ Odd s)
    (h₁ : ∀ s ∈ S₁, QuadraticSieveBound M (N₁ / s) K₁)
    (h₂ : ∀ s ∈ S₂, QuadraticSieveBound M (N₂ / s) K₂) (a b : ℕ → ℂ) :
    (∑ s₁ ∈ S₁, ∑ s₂ ∈ S₂, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * S₁.card * quadraticDivisorMoment N₁ a) *
      Real.sqrt (2 * K₂ * S₂.card * quadraticDivisorMoment N₂ b) := by
  calc
    _ ≤ ∑ s₁ ∈ S₁, ∑ s₂ ∈ S₂,
        Real.sqrt (2 * K₁ * quadraticDivisorWeight N₁ s₁ a) *
        Real.sqrt (2 * K₂ * quadraticDivisorWeight N₂ s₂ b) := by
      apply Finset.sum_le_sum
      intro s₁ hs₁'
      apply Finset.sum_le_sum
      intro s₂ hs₂'
      exact quadratic_coprime_restricted_bound (hs₁ s₁ hs₁').1 (hs₁ s₁ hs₁').2
        (hs₂ s₂ hs₂').1 (hs₂ s₂ hs₂').2 hK₁ hK₂ (h₁ s₁ hs₁') (h₂ s₂ hs₂') a b
    _ = (∑ s₁ ∈ S₁, Real.sqrt (2 * K₁ * quadraticDivisorWeight N₁ s₁ a)) *
        ∑ s₂ ∈ S₂, Real.sqrt (2 * K₂ * quadraticDivisorWeight N₂ s₂ b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul (quadratic_divisor_weight_sqrt_sum N₁ S₁ K₁ hK₁ a)
      (quadratic_divisor_weight_sqrt_sum N₂ S₂ K₂ hK₂ b)
      (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorMomentBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the divisor moment by an arbitrarily small power -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_divisor_moment_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ a : ℕ → ℂ,
      quadraticDivisorMoment N a ≤ C * (N : ℝ) ^ ε * quadraticSieveEnergy N a := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_bound (ε / 2) (by positivity)
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro N a
  unfold quadraticDivisorMoment quadraticSieveEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 := (Finset.mem_filter.mp hn).2.2.ne_zero
  have hnN : (n : ℝ) ≤ N := by
    exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
  have hdiv : (n.divisors.card : ℝ) ≤ C * (N : ℝ) ^ (ε / 2) :=
    (hc n hn0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnN (by positivity)) hC.le)
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg n.divisors.card) hdiv 2
  have he : (C * (N : ℝ) ^ (ε / 2)) ^ 2 = C ^ 2 * (N : ℝ) ^ ε := by
    rw [mul_pow]
    congr 1
    calc
      _ = ((N : ℝ) ^ (ε / 2)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = (N : ℝ) ^ ((ε / 2) * 2) := (Real.rpow_mul (Nat.cast_nonneg N) _ _).symm
      _ = _ := by congr 1; ring
  rw [he] at hsq
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorRectangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite divisor rectangle underlying the bilinear estimate -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem mem_oddSquarefreeRange_of_dvd {s n N : ℕ} (hn : n ∈ oddSquarefreeRange N)
    (hs : s ∣ n) : s ∈ oddSquarefreeRange N := by
  obtain ⟨hr, ho, hsq⟩ := Finset.mem_filter.mp hn
  have hsm : s ∈ n.divisors := Nat.mem_divisors.mpr ⟨hs, hsq.ne_zero⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨Nat.pos_of_mem_divisors hsm, (Nat.le_of_dvd (Finset.mem_Icc.mp hr).1 hs).trans
      (Finset.mem_Icc.mp hr).2⟩,
    ho.of_dvd_nat hs, hsq.squarefree_of_dvd hs⟩

 theorem quadratic_restricted_bilinear_zero_left {N₁ N₂ s₁ s₂ : ℕ}
    (hs : s₁ ∉ oddSquarefreeRange N₁) (a b : ℕ → ℂ) (m : ℤ) :
    quadraticCoprimeBilinear N₁ N₂ (fun n => if s₁ ∣ n then a n else 0)
      (fun n => if s₂ ∣ n then b n else 0) m = 0 := by
  unfold quadraticCoprimeBilinear
  apply Finset.sum_eq_zero
  intro n₁ hn₁
  apply Finset.sum_eq_zero
  intro n₂ _
  have hd : ¬s₁ ∣ n₁ := fun h => hs (mem_oddSquarefreeRange_of_dvd hn₁ h)
  simp [hd]

 theorem quadratic_restricted_bilinear_zero_right {N₁ N₂ s₁ s₂ : ℕ}
    (hs : s₂ ∉ oddSquarefreeRange N₂) (a b : ℕ → ℂ) (m : ℤ) :
    quadraticCoprimeBilinear N₁ N₂ (fun n => if s₁ ∣ n then a n else 0)
      (fun n => if s₂ ∣ n then b n else 0) m = 0 := by
  unfold quadraticCoprimeBilinear
  apply Finset.sum_eq_zero
  intro n₁ _
  apply Finset.sum_eq_zero
  intro n₂ hn₂
  have hd : ¬s₂ ∣ n₂ := fun h => hs (mem_oddSquarefreeRange_of_dvd hn₂ h)
  simp [hd]

 theorem quadratic_restricted_bilinear_support {N₁ N₂ s₁ s₂ : ℕ}
    (a b : ℕ → ℂ) (m : ℤ)
    (h : quadraticCoprimeBilinear N₁ N₂ (fun n => if s₁ ∣ n then a n else 0)
      (fun n => if s₂ ∣ n then b n else 0) m ≠ 0) :
    s₁ ∈ oddSquarefreeRange N₁ ∧ s₂ ∈ oddSquarefreeRange N₂ := by
  constructor
  · by_contra hs
    exact h (quadratic_restricted_bilinear_zero_left hs a b m)
  · by_contra hs
    exact h (quadratic_restricted_bilinear_zero_right hs a b m)

 theorem quadratic_divisor_bilinear_rectangle (N₁ N₂ d : ℕ) (hd : 0 < d)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticDivisorBilinear N₁ N₂ d a b m =
      ∑ z ∈ (oddSquarefreeRange N₁).product (oddSquarefreeRange N₂),
        if z.1 * z.2 = d then quadraticCoprimeBilinear N₁ N₂
          (fun n => if z.1 ∣ n then a n else 0)
          (fun n => if z.2 ∣ n then b n else 0) m else 0 := by
  rw [quadratic_divisor_bilinear_split N₁ N₂ d hd]
  apply Finset.sum_bij_ne_zero (fun e _ _ => (e, d / e))
  · intro e _ he
    exact Finset.mem_product.mpr (quadratic_restricted_bilinear_support a b m he)
  · intro e _ _ f _ _ hef
    exact congrArg Prod.fst hef
  · intro z hz hz0
    have heq : z.1 * z.2 = d := by
      by_contra heq
      simp only [ite_eq_right heq] at hz0
      exact hz0 rfl
    have hzpos : 0 < z.1 :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1).1
    have hdiv : d / z.1 = z.2 :=
      Nat.div_eq_of_eq_mul_left hzpos (by simpa only [mul_comm] using heq.symm)
    refine ⟨z.1, Nat.mem_divisors.mpr ⟨⟨z.2, heq.symm⟩, hd.ne'⟩, ?_, ?_⟩
    · simpa only [ite_eq_left heq, hdiv] using hz0
    · exact Prod.ext rfl hdiv
  · intro e he _
    have heq : e * (d / e) = d := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)
    exact (ite_eq_left heq).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounding the original product-divisibility sum by its exact rectangle -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_divisor_range_triangle (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
    ∑ z ∈ quadraticDivisorRangePairs N₁ N₂ D, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if z.1 ∣ n then a n else 0)
        (fun n => if z.2 ∣ n then b n else 0) m‖ := by
  let R := (oddSquarefreeRange N₁).product (oddSquarefreeRange N₂)
  let F : ℕ × ℕ → ℝ := fun z => ∑ m ∈ oddSquarefreeRange M,
    ‖quadraticCoprimeBilinear N₁ N₂
      (fun n => if z.1 ∣ n then a n else 0)
      (fun n => if z.2 ∣ n then b n else 0) m‖
  have hp (d : ℕ) (hd : 0 < d) :
      (∑ m ∈ oddSquarefreeRange M, ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
        ∑ z ∈ R, if z.1 * z.2 = d then F z else 0 := by
    calc
      _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ z ∈ R,
          if z.1 * z.2 = d then
            ‖quadraticCoprimeBilinear N₁ N₂
              (fun n => if z.1 ∣ n then a n else 0)
              (fun n => if z.2 ∣ n then b n else 0) m‖ else 0 := by
        apply Finset.sum_le_sum
        intro m _
        rw [quadratic_divisor_bilinear_rectangle N₁ N₂ d hd]
        apply (norm_sum_le _ _).trans_eq
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z.1 * z.2 = d <;> simp [hz, F]
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ z ∈ R,
        if z.1 * z.2 = d then F z else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      exact hp d (lt_of_le_of_lt (Nat.zero_le D) (Finset.mem_Ioc.mp hd).1)
    _ = ∑ z ∈ R, if D < z.1 * z.2 ∧ z.1 * z.2 ≤ 2 * D then F z else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      simp only [Finset.sum_ite_eq, Finset.mem_Ioc]
    _ = _ := by rw [← Finset.sum_filter]; rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A disjoint dyadic partition of the actual odd-squarefree divisors -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticDyadicDivisors_bounds {N j s : ℕ}
    (hs : s ∈ quadraticDyadicDivisors N j) : 2 ^ j ≤ s ∧ s < 2 ^ (j + 1) := by
  obtain ⟨hs, hj⟩ := Finset.mem_filter.mp hs
  have hn := (Finset.mem_filter.mp hs).2.2.ne_zero
  have hlo := Nat.pow_log_le_self 2 hn
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) s
  rw [hj] at hlo hhi
  exact ⟨hlo, hhi⟩

 theorem quadraticDyadicDivisors_card (N j : ℕ) :
    (quadraticDyadicDivisors N j).card ≤ 2 ^ j := by
  have hs : quadraticDyadicDivisors N j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)) := by
    intro s hs
    exact Finset.mem_Ico.mpr (quadraticDyadicDivisors_bounds hs)
  calc
    _ ≤ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card := Finset.card_le_card hs
    _ = 2 ^ j := by rw [Nat.card_Ico, pow_succ]; omega

 theorem quadratic_dyadic_divisors_sum {R : Type*} [AddCommMonoid R]
    (N : ℕ) (f : ℕ → R) :
    (∑ j ∈ Finset.range (Nat.log 2 N + 1), ∑ s ∈ quadraticDyadicDivisors N j, f s) =
      ∑ s ∈ oddSquarefreeRange N, f s := by
  simp only [quadraticDyadicDivisors, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hle : Nat.log 2 s < Nat.log 2 N + 1 := by
    have hh := Nat.log_mono_right (b := 2)
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
    omega
  simp only [Finset.sum_ite_eq, Finset.mem_range, hle, ite_true, if_true]

 theorem quadratic_dyadic_pair_sum {R : Type*} [AddCommMonoid R]
    (N₁ N₂ : ℕ) (f : ℕ → ℕ → R) :
    (∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ j ∈ Finset.range (Nat.log 2 N₂ + 1),
      ∑ s ∈ quadraticDyadicDivisors N₁ i, ∑ t ∈ quadraticDyadicDivisors N₂ j, f s t) =
      ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂, f s t := by
  calc
    _ = ∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ s ∈ quadraticDyadicDivisors N₁ i,
        ∑ j ∈ Finset.range (Nat.log 2 N₂ + 1), ∑ t ∈ quadraticDyadicDivisors N₂ j, f s t :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ s ∈ quadraticDyadicDivisors N₁ i,
        ∑ t ∈ oddSquarefreeRange N₂, f s t := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun s _ => quadratic_dyadic_divisors_sum N₂ (f s))
    _ = _ := quadratic_dyadic_divisors_sum N₁ _

 theorem quadratic_dyadic_divisor_family_bound (M N₁ N₂ i j : ℕ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (N₁ / 2 ^ i) K₁)
    (h₂ : QuadraticSieveBound M (N₂ / 2 ^ j) K₂) (a b : ℕ → ℂ) :
    (∑ s₁ ∈ quadraticDyadicDivisors N₁ i, ∑ s₂ ∈ quadraticDyadicDivisors N₂ j,
      ∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
      Real.sqrt (2 * K₂ * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) := by
  have hs (N k s : ℕ) (h : s ∈ quadraticDyadicDivisors N k) :
      Squarefree s ∧ Odd s := by
    obtain ⟨hr, _⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_filter.mp hr).2.2, (Finset.mem_filter.mp hr).2.1⟩
  have hcut₁ : ∀ s ∈ quadraticDyadicDivisors N₁ i,
      QuadraticSieveBound M (N₁ / s) K₁ := by
    intro s hs'
    exact QuadraticSieveBound.mono_second (Nat.div_le_div_left
      (quadraticDyadicDivisors_bounds hs').1 (by positivity)) h₁
  have hcut₂ : ∀ s ∈ quadraticDyadicDivisors N₂ j,
      QuadraticSieveBound M (N₂ / s) K₂ := by
    intro s hs'
    exact QuadraticSieveBound.mono_second (Nat.div_le_div_left
      (quadraticDyadicDivisors_bounds hs').1 (by positivity)) h₂
  apply (quadratic_divisor_family_bound M N₁ N₂ _ _ K₁ K₂ hK₁ hK₂
    (hs N₁ i) (hs N₂ j) hcut₁ hcut₂ a b).trans
  apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast quadraticDyadicDivisors_card N₁ i)
        (by positivity)) (quadraticDivisorMoment_nonneg N₁ a)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast quadraticDyadicDivisors_card N₂ j)
        (by positivity)) (quadraticDivisorMoment_nonneg N₂ b)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a genuine divisor block with the original product range -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_dyadic_divisor_mass_total (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ) :
    (∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ j ∈ Finset.range (Nat.log 2 N₂ + 1),
      quadraticDyadicDivisorMass M N₁ N₂ D i j a b) =
      ∑ z ∈ quadraticDivisorRangePairs N₁ N₂ D, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticCoprimeBilinear N₁ N₂
          (fun n => if z.1 ∣ n then a n else 0)
          (fun n => if z.2 ∣ n then b n else 0) m‖ := by
  unfold quadraticDyadicDivisorMass
  rw [quadratic_dyadic_pair_sum]
  rw [quadraticDivisorRangePairs, Finset.sum_filter, Finset.product_eq_sprod,
    Finset.sum_product]

 theorem quadratic_positive_block_product_bounds {M N₁ N₂ D i j : ℕ} (a b : ℕ → ℂ)
    (h : 0 < quadraticDyadicDivisorMass M N₁ N₂ D i j a b) :
    D < 4 * (2 ^ i * 2 ^ j) ∧ 2 ^ i * 2 ^ j ≤ 2 * D := by
  have hw (s t : ℕ) : 0 ≤
      (if D < s * t ∧ s * t ≤ 2 * D then
        ∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂
          (fun n => if s ∣ n then a n else 0)
          (fun n => if t ∣ n then b n else 0) m‖ else 0) := by
    split_ifs
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · rfl
  obtain ⟨s, hs, hsum⟩ := (Finset.sum_pos_iff_of_nonneg (fun s _ =>
    Finset.sum_nonneg (fun t _ => hw s t))).mp h
  obtain ⟨t, ht, hp⟩ := (Finset.sum_pos_iff_of_nonneg (fun t _ => hw s t)).mp hsum
  have hd : D < s * t ∧ s * t ≤ 2 * D := by
    by_contra hd
    simp only [ite_eq_right hd, lt_self_iff_false] at hp
  obtain ⟨hsl, hsu⟩ := quadraticDyadicDivisors_bounds hs
  obtain ⟨htl, htu⟩ := quadraticDyadicDivisors_bounds ht
  have hlo := Nat.mul_le_mul hsl htl
  have hhi := Nat.mul_lt_mul_of_lt_of_lt hsu htu
  rw [pow_succ, pow_succ] at hhi
  constructor
  · nlinarith [hd.1]
  · exact hlo.trans hd.2

 theorem quadratic_divisor_block_selection (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (hpos : 0 < ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) :
    ∃ i ≤ Nat.log 2 N₁, ∃ j ≤ Nat.log 2 N₂,
      0 < quadraticDyadicDivisorMass M N₁ N₂ D i j a b ∧
      D < 4 * (2 ^ i * 2 ^ j) ∧ 2 ^ i * 2 ^ j ≤ 2 * D ∧
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) *
        quadraticDyadicDivisorMass M N₁ N₂ D i j a b := by
  let J := (Finset.range (Nat.log 2 N₁ + 1)).product (Finset.range (Nat.log 2 N₂ + 1))
  let F : ℕ × ℕ → ℝ := fun z => quadraticDyadicDivisorMass M N₁ N₂ D z.1 z.2 a b
  have hJ : J.Nonempty := ⟨(0, 0), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image J F hJ
  have hsum : (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * F z := by
    calc
      _ ≤ ∑ w ∈ J, F w := by
        rw [show J = (Finset.range (Nat.log 2 N₁ + 1)).product
          (Finset.range (Nat.log 2 N₂ + 1)) from rfl,
          Finset.product_eq_sprod, Finset.sum_product]
        rw [quadratic_dyadic_divisor_mass_total]
        exact quadratic_divisor_range_triangle M N₁ N₂ D a b
      _ ≤ J.card • F z := Finset.sum_le_card_nsmul J F (F z) hmax
      _ = _ := by simp [J, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
  have hblock : 0 < F z := by
    by_contra! hn
    have hz' : ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * F z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hn
    exact (not_lt_of_ge (hsum.trans hz')) hpos
  obtain ⟨h₁, h₂⟩ := quadratic_positive_block_product_bounds a b hblock
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hz
  exact ⟨z.1, by have := Finset.mem_range.mp hi; omega,
    z.2, by have := Finset.mem_range.mp hj; omega, hblock, h₁, h₂, hsum⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticBilinearComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor-constrained comparison with concrete selected scales

This is the finite comparison of Heath-Brown (1995), Lemma 10. We retain the
explicit number of dyadic bins instead of enlarging the selected scales to
hide logarithms. All quadratic matrix bounds are at the actual shorter ranges.
-/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_dyadic_divisor_mass_bound (M N₁ N₂ D i j : ℕ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (N₁ / 2 ^ i) K₁)
    (h₂ : QuadraticSieveBound M (N₂ / 2 ^ j) K₂) (a b : ℕ → ℂ) :
    quadraticDyadicDivisorMass M N₁ N₂ D i j a b ≤
      Real.sqrt (2 * K₁ * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
      Real.sqrt (2 * K₂ * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) := by
  apply le_trans _ (quadratic_dyadic_divisor_family_bound M N₁ N₂ i j
    K₁ K₂ hK₁ hK₂ h₁ h₂ a b)
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro t _
  split_ifs
  · rfl
  · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

 theorem quadratic_bilinear_comparison (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (hpos : 0 < ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) :
    ∃ i ≤ Nat.log 2 N₁, ∃ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) ∧ 2 ^ i * 2 ^ j ≤ 2 * D ∧
      ∀ K₁ K₂ : ℝ, 0 ≤ K₁ → 0 ≤ K₂ →
      QuadraticSieveBound M (N₁ / 2 ^ i) K₁ →
      QuadraticSieveBound M (N₂ / 2 ^ j) K₂ →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) *
        (Real.sqrt (2 * K₁ * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
          Real.sqrt (2 * K₂ * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b)) := by
  obtain ⟨i, hi, j, hj, _, hD₁, hD₂, hb⟩ := quadratic_divisor_block_selection
    M N₁ N₂ D a b hpos
  refine ⟨i, hi, j, hj, hD₁, hD₂, ?_⟩
  intro K₁ K₂ hK₁ hK₂ h₁ h₂
  exact hb.trans (mul_le_mul_of_nonneg_left
    (quadratic_dyadic_divisor_mass_bound M N₁ N₂ D i j K₁ K₂ hK₁ hK₂ h₁ h₂ a b)
    (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the small-kernel conductor divisors into the fixed and pair parts -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_coprime_divisor_sum {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (F : ℕ → ℂ) :
    (∑ d ∈ (m * n).divisors, F d) =
      ∑ e ∈ m.divisors, ∑ f ∈ n.divisors, F (e * f) := by
  symm
  rw [← Finset.sum_product m.divisors n.divisors (fun z => F (z.1 * z.2))]
  have hleft (z : ℕ × ℕ) (hz : z ∈ m.divisors.product n.divisors) :
      z.1 = (z.1 * z.2).gcd m := by
    obtain ⟨hz₁, hz₂⟩ := Finset.mem_product.mp hz
    have he := Nat.pos_of_mem_divisors hz₁
    have hf := Nat.pos_of_mem_divisors hz₂
    apply quadratic_divisor_split_unique (Nat.mul_pos he hf).ne' hcop
      (dvd_mul_right z.1 z.2) (Nat.dvd_of_mem_divisors hz₁)
    simpa only [Nat.mul_div_cancel_left _ he] using Nat.dvd_of_mem_divisors hz₂
  apply Finset.sum_bij (fun z _ => z.1 * z.2)
  · intro z hz
    obtain ⟨he, hf⟩ := Finset.mem_product.mp hz
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors he)
      (Nat.dvd_of_mem_divisors hf), (Nat.mul_pos hm hn).ne'⟩
  · intro z hz w hw heq
    have hfst : z.1 = w.1 := by rw [hleft z hz, hleft w hw, heq]
    have hz₀ : z.1 ≠ 0 := (Nat.pos_of_mem_divisors (Finset.mem_product.mp hz).1).ne'
    have hsnd : z.2 = w.2 := by
      rw [← hfst] at heq
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hz₀) heq
    exact Prod.ext hfst hsnd
  · intro d hd
    have hd₀ := Nat.pos_of_mem_divisors hd
    obtain ⟨he, hem, hfn⟩ := quadratic_divisor_split_exists hd₀ hcop (Nat.dvd_of_mem_divisors hd)
    refine ⟨(d.gcd m, d / d.gcd m), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨hem, hm.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨hfn, hn.ne'⟩
    · exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)
  · intro z _
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorDyadicPartition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Disjoint divisor blocks, including the divisor-one boundary -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticDivisorDyadicBlock_subset (Q j : ℕ) :
    quadraticDivisorDyadicBlock Q j ⊆ Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
  intro d hd
  obtain ⟨hd, hj⟩ := Finset.mem_filter.mp hd
  have hd₂ := (Finset.mem_Icc.mp hd).1
  have hn : d - 1 ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 2 hn
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (d - 1)
  rw [hj] at hlo hhi
  rw [pow_succ] at hhi
  apply Finset.mem_Ioc.mpr
  omega

theorem quadratic_divisor_dyadic_sum {R : Type*} [AddCommMonoid R] (Q : ℕ) (F : ℕ → R) :
    (∑ j ∈ Finset.range (Nat.log 2 Q + 1),
      ∑ d ∈ quadraticDivisorDyadicBlock Q j, F d) = ∑ d ∈ Finset.Icc 2 Q, F d := by
  simp only [quadraticDivisorDyadicBlock, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : Nat.log 2 (d - 1) < Nat.log 2 Q + 1 := by
    have hh := Nat.log_mono_right (b := 2)
      (show d - 1 ≤ Q by have := (Finset.mem_Icc.mp hd).2; omega)
    omega
  simp only [Finset.sum_ite_eq, Finset.mem_range, hle, ite_true, if_true]

theorem quadratic_divisor_sum_one_blocks {R : Type*} [AddCommMonoid R]
    {Q : ℕ} (hQ : 1 ≤ Q) (F : ℕ → R) :
    (∑ d ∈ Finset.Icc 1 Q, F d) = F 1 +
      ∑ j ∈ Finset.range (Nat.log 2 Q + 1), ∑ d ∈ quadraticDivisorDyadicBlock Q j, F d := by
  rw [quadratic_divisor_dyadic_sum]
  have hmem : 1 ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩
  have heq : (Finset.Icc 1 Q).erase 1 = Finset.Icc 2 Q := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  rw [← heq, Finset.add_sum_erase _ _ hmem]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact correction blocks retain the joint frequency sums -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticDivisorDyadicBlock_eq_filter (Q j : ℕ) :
    quadraticDivisorDyadicBlock Q j =
      (Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter (fun d => d ≤ Q) := by
  classical
  ext d
  constructor
  · intro hd
    exact Finset.mem_filter.mpr ⟨quadraticDivisorDyadicBlock_subset Q j hd,
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2⟩
  · intro hd
    obtain ⟨hd, hQ⟩ := Finset.mem_filter.mp hd
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hd
    have hp : 1 ≤ (2 : ℕ) ^ j := one_le_pow₀ (by norm_num)
    have hl : 2 ^ j ≤ d - 1 := by omega
    have hu : d - 1 < 2 ^ (j + 1) := by rw [pow_succ]; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hQ⟩,
      Nat.log_eq_of_pow_le_of_lt_pow hl hu⟩

theorem quadratic_correction_divisor_sum {Q : ℕ} (hQ : 1 ≤ Q) (F : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 Q, F d) = F 1 +
      ∑ j ∈ Finset.range (Nat.log 2 Q + 1),
        ∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0 := by
  rw [quadratic_divisor_sum_one_blocks hQ]
  simp_rw [quadraticDivisorDyadicBlock_eq_filter, Finset.sum_filter]

theorem quadratic_correction_divisor_bound {Q : ℕ} (hQ : 1 ≤ Q)
    (F : ℕ → ℂ) (A : ℝ) (T : ℕ → ℝ) (hunit : ‖F 1‖ ≤ A)
    (hblock : ∀ j < Nat.log 2 Q + 1,
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ T j) :
    ‖∑ d ∈ Finset.Icc 1 Q, F d‖ ≤ A + ∑ j ∈ Finset.range (Nat.log 2 Q + 1), T j := by
  rw [quadratic_correction_divisor_sum hQ]
  apply (norm_add_le _ _).trans
  exact add_le_add hunit ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j hj => hblock j (Finset.mem_range.mp hj)))

theorem quadraticDyadicDivisors_eq_filter (K j : ℕ) :
    quadraticDyadicDivisors K j = (oddSquarefreeRange (2 * 2 ^ j)).filter
      (fun b => 2 ^ j ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ j) := by
  classical
  ext b
  constructor
  · intro hb
    have hbounds := quadraticDyadicDivisors_bounds hb
    obtain ⟨hb, _⟩ := Finset.mem_filter.mp hb
    obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hb
    rw [pow_succ] at hbounds
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by omega⟩, ho, hsf⟩,
      hbounds.1, (Finset.mem_Icc.mp hr).2, ?_⟩
    omega
  · intro hb
    obtain ⟨hb, hlo, hK, hhi⟩ := Finset.mem_filter.mp hb
    obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, hK⟩, ho, hsf⟩, ?_⟩
    apply Nat.log_eq_of_pow_le_of_lt_pow hlo
    rw [pow_succ]
    omega

theorem quadratic_correction_frequency_sum (K : ℕ) (F : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeRange K, F b) =
      ∑ j ∈ Finset.range (Nat.log 2 K + 1), ∑ b ∈ oddSquarefreeRange (2 * 2 ^ j),
        if 2 ^ j ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ j then F b else 0 := by
  rw [← quadratic_dyadic_divisors_sum K F]
  simp_rw [quadraticDyadicDivisors_eq_filter, Finset.sum_filter]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyAggregation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency aggregation preserves each complete divisor comparison -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_correction_frequency_reindex (K Q : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K, F d b) =
      ∑ i ∈ Finset.range (Nat.log 2 K + 1), ∑ d ∈ Finset.Icc 1 Q,
        ∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
          if 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F d b else 0 := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 Q, ∑ i ∈ Finset.range (Nat.log 2 K + 1),
        ∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
          if 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F d b else 0 :=
      Finset.sum_congr rfl (fun d _ => quadratic_correction_frequency_sum K (F d))
    _ = _ := Finset.sum_comm

theorem quadratic_correction_frequency_bound (K Q : ℕ) (F : ℕ → ℕ → ℂ) (c : ℂ)
    (T : ℝ) (hband : ∀ i < Nat.log 2 K + 1,
      ‖c * (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * 2 ^ i),
        if 2 ^ i ≤ b ∧ b ≤ K ∧ b < 2 * 2 ^ i then F d b else 0)‖ ≤ T) :
    ‖c * (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange K, F d b)‖ ≤
      ((Nat.log 2 K + 1 : ℕ) : ℝ) * T := by
  rw [quadratic_correction_frequency_reindex, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range (Nat.log 2 K + 1), T :=
      Finset.sum_le_sum (fun i hi => hband i (Finset.mem_range.mp hi))
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem quadratic_frequency_block_le {K i : ℕ} (hK : 0 < K) (hi : i < Nat.log 2 K + 1) :
    2 ^ i ≤ K :=
  (Nat.pow_le_pow_right (by norm_num) (by omega : i ≤ Nat.log 2 K)).trans
    (Nat.pow_log_le_self 2 hK.ne')

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUniformBilinear
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound over the finitely many actual divisor scales -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_bilinear_uniform_bound (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 N₂, 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T := by
  by_cases hp : 0 < ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖
  · obtain ⟨i, hi, j, hj, hD₁, hD₂, hb⟩ := quadratic_bilinear_comparison M N₁ N₂ D a b hp
    exact (hb (K₁ i) (K₂ j) (hK₁ i hi) (hK₂ j hj) (h₁ i hi) (h₂ j hj)).trans
      (mul_le_mul_of_nonneg_left (hcost i hi j hj hD₁ hD₂) (by positivity))
  · exact (le_of_not_gt hp).trans (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelEnvelope
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The numerical small-kernel error and the literal exponent factors -/

namespace Ostmann

theorem quadratic_small_kernel_envelope {M N B P Y D : ℝ}
    (hM : 0 < M) (hN : 0 ≤ N) (hB : 0 < B) (hP : 1 ≤ P) (hY : 0 ≤ Y)
    (hD : 0 ≤ D) (hcut : Real.sqrt M / (Real.sqrt B * P) ≤ D) :
    (Real.sqrt M / (Real.sqrt B * Real.sqrt P)) *
      (Y + Real.sqrt (Y * N) + N / Real.sqrt P) ≤
        2 * (Real.sqrt M / Real.sqrt B * Y + D * N) := by
  have hP₀ : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let R := Real.sqrt M / (Real.sqrt B * Real.sqrt P)
  let A := Real.sqrt M / Real.sqrt B * Y
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsp : Real.sqrt P ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hP₀)
  have hsb : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  have hsp₁ : 1 ≤ Real.sqrt P := (Real.le_sqrt (by norm_num) hP₀.le).2 (by simpa using hP)
  have hfirst : R * Y ≤ A := by
    dsimp [R, A]
    apply mul_le_mul_of_nonneg_right _ hY
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg M) (Real.sqrt_pos.2 hB)
      (by nlinarith [Real.sqrt_nonneg B])
  have hthird : R * (N / Real.sqrt P) ≤ D * N := by
    calc
      _ = (Real.sqrt M / (Real.sqrt B * P)) * N := by
        dsimp [R]
        rw [div_mul_div_comm]
        have hs : Real.sqrt B * Real.sqrt P * Real.sqrt P = Real.sqrt B * P := by
          rw [mul_assoc, ← pow_two, Real.sq_sqrt hP₀.le]
        rw [hs]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcut hN
  have hcrosssq : (R * Real.sqrt (Y * N)) ^ 2 ≤ A * (D * N) := by
    calc
      _ = A * ((Real.sqrt M / (Real.sqrt B * P)) * N) := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hY hN)]
        dsimp [R, A]
        field_simp
        nlinarith only [congrArg (fun z : ℝ => z * Y * N) (Real.sq_sqrt hP₀.le)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcut hN) hA
  have hcross : R * Real.sqrt (Y * N) ≤ (A + D * N) / 2 := by
    have hc : 0 ≤ R * Real.sqrt (Y * N) := mul_nonneg hR (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg (A - D * N), mul_nonneg hD hN]
  change R * (Y + Real.sqrt (Y * N) + N / Real.sqrt P) ≤ 2 * (A + D * N)
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTwoScaleCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual shortened matrix ranges in the quadratic comparison -/

namespace Ostmann

private theorem sqrt_add_subadditive {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hxy := Real.sq_sqrt (add_nonneg hx hy)
  have hxs := Real.sq_sqrt hx
  have hys := Real.sq_sqrt hy
  have hn := Real.sqrt_nonneg (x + y)
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

theorem quadratic_two_scale_sqrt_cost {Y N u v : ℝ}
    (hY : 0 ≤ Y) (hN : 0 ≤ N) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v) ≤
      Y + 2 * Real.sqrt (Y * N) + N / Real.sqrt (u * v) := by
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have hv₀ : 0 < v := zero_lt_one.trans_le hv
  have hsu : Real.sqrt (N / u) ≤ Real.sqrt N := Real.sqrt_le_sqrt
    ((div_le_self hN hu).trans_eq rfl)
  have hsv : Real.sqrt (N / v) ≤ Real.sqrt N := Real.sqrt_le_sqrt
    ((div_le_self hN hv).trans_eq rfl)
  have hprod : Real.sqrt (N / u) * Real.sqrt (N / v) = N / Real.sqrt (u * v) := by
    rw [Real.sqrt_div hN, Real.sqrt_div hN, div_mul_div_comm,
      ← pow_two, Real.sq_sqrt hN, ← Real.sqrt_mul hu₀.le]
  calc
    _ ≤ (Real.sqrt Y + Real.sqrt (N / u)) * (Real.sqrt Y + Real.sqrt (N / v)) :=
      mul_le_mul (sqrt_add_subadditive hY (div_nonneg hN hu₀.le))
        (sqrt_add_subadditive hY (div_nonneg hN hv₀.le))
        (Real.sqrt_nonneg _) (by positivity)
    _ = Y + Real.sqrt Y * Real.sqrt (N / u) + Real.sqrt Y * Real.sqrt (N / v) +
        N / Real.sqrt (u * v) := by
      rw [← hprod]
      nlinarith only [Real.sq_sqrt hY]
    _ ≤ Y + Real.sqrt Y * Real.sqrt N + Real.sqrt Y * Real.sqrt N +
        N / Real.sqrt (u * v) := by
      gcongr
    _ = _ := by rw [Real.sqrt_mul hY]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveDuality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity and duality interchange the two quadratic-sieve lengths -/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

 theorem QuadraticSieveBound.transpose {M N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (h : QuadraticSieveBound N M K) : QuadraticSieveBound M N (2 * K) := by
  let U := oddSquarefreeRange M
  let V := oddSquarefreeRange N
  let F : Matrix U V ℂ := .of (fun m n => (jacobiSym (n.val : ℤ) m.val : ℂ))
  have hdual (b : U → ℂ) :
      (∑ n : V, ‖(Fᴴ *ᵥ b) n‖ ^ 2) ≤ 2 * K * ∑ m : U, ‖b m‖ ^ 2 := by
    let b' : ℕ → ℂ := fun m => if hm : m ∈ U then b ⟨m, hm⟩ else 0
    have hE : quadraticSieveEnergy M b' = ∑ m : U, ‖b m‖ ^ 2 := by
      symm
      calc
        _ = ∑ m : U, ‖b' m.val‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro m _
          simp [b']
        _ = ∑ m ∈ U, ‖b' m‖ ^ 2 := Finset.sum_coe_sort U (fun m : ℕ => ‖b' m‖ ^ 2)
    have hpoint (n : V) : (Fᴴ *ᵥ b) n = quadraticTransposeSum M b' n.val := by
      change (∑ m : U, star ((jacobiSym (n.val : ℤ) m.val : ℂ)) * b m) = _
      calc
        _ = ∑ m : U, b' m.val * (jacobiSym (n.val : ℤ) m.val : ℂ) := by
          apply Finset.sum_congr rfl
          intro m _
          simp only [star_intCast]
          simp [b', mul_comm]
        _ = _ := Finset.sum_coe_sort U (fun m : ℕ => b' m * (jacobiSym (n.val : ℤ) m : ℂ))
    have hsum : (∑ n : V, ‖(Fᴴ *ᵥ b) n‖ ^ 2) =
        ∑ n ∈ V, ‖quadraticTransposeSum M b' n‖ ^ 2 := by
      calc
        _ = ∑ n : V, ‖quadraticTransposeSum M b' n.val‖ ^ 2 := by simp_rw [hpoint]
        _ = _ := Finset.sum_coe_sort V (fun n : ℕ => ‖quadraticTransposeSum M b' n‖ ^ 2)
    rw [hsum, ← hE]
    exact quadraticTranspose_of_bound h b'
  intro b
  have hb := finite_matrix_duality F (2 * K) (by positivity) hdual (fun n => b n.val)
  have hpoint (m : U) : (F *ᵥ fun n => b n.val) m = quadraticSieveSum N b m.val := by
    change (∑ n : V, (jacobiSym (n.val : ℤ) m.val : ℂ) * b n.val) = _
    calc
      _ = ∑ n : V, b n.val * (jacobiSym (n.val : ℤ) m.val : ℂ) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = _ := Finset.sum_coe_sort V (fun n : ℕ => b n * (jacobiSym (n : ℤ) m.val : ℂ))
  have hleft : (∑ m : U, ‖(F *ᵥ fun n => b n.val) m‖ ^ 2) =
      ∑ m ∈ U, ‖quadraticSieveSum N b m‖ ^ 2 := by
    calc
      _ = ∑ m : U, ‖quadraticSieveSum N b m.val‖ ^ 2 := by simp_rw [hpoint]
      _ = _ := Finset.sum_coe_sort U (fun m : ℕ => ‖quadraticSieveSum N b m‖ ^ 2)
  have hright : (∑ n : V, ‖b n.val‖ ^ 2) = quadraticSieveEnergy N b :=
    Finset.sum_coe_sort V (fun n : ℕ => ‖b n‖ ^ 2)
  rw [hleft, hright] at hb
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise exponent induction for the actual quadratic-sieve matrices -/

namespace Ostmann

theorem quadratic_growth_shortened_transpose {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B N d : ℕ, 1 ≤ B → 1 ≤ d → d ≤ N →
      QuadraticSieveBound B (N / d)
        (C * ((B : ℝ) * N) ^ ε * ((B : ℝ) ^ ξ + (N : ℝ) / d)) := by
  obtain ⟨C, hC, hc⟩ := h ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro B N d hB hd hdN
  have hdiv : 1 ≤ N / d := Nat.div_pos hdN hd
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hDR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := by exact_mod_cast hd.trans hdN
  have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hfloorN : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N d
  have hfactor : 0 ≤ C * (((N / d : ℕ) : ℝ) * B) ^ ε * (((N / d : ℕ) : ℝ) + (B : ℝ) ^ ξ) := by positivity
  apply ((hc (N / d) B hdiv hB).transpose hfactor).mono_constant
  have hp : (((N / d : ℕ) : ℝ) * B) ^ ε ≤ ((B : ℝ) * N) ^ ε := by
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    nlinarith [mul_le_mul_of_nonneg_right hfloorN hBR.le]
  calc
    _ = (2 * C) * (((N / d : ℕ) : ℝ) * B) ^ ε * ((B : ℝ) ^ ξ + ((N / d : ℕ) : ℝ)) := by ring
    _ ≤ _ := by gcongr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthMatrixCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common matrix budget for each actual divisor band -/

namespace Ostmann

private theorem root_product_factor {F Y N u v E₁ E₂ : ℝ}
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hN : 0 ≤ N)
    (hu : 0 < u) (hv : 0 < v) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) :
    Real.sqrt (2 * (F * (Y + N / u)) * u * E₁) *
      Real.sqrt (2 * (F * (Y + N / v)) * v * E₂) =
      2 * F * Real.sqrt (u * v) *
        (Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v)) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by
  have ha : 0 ≤ Y + N / u := by positivity
  have hb : 0 ≤ Y + N / v := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (F * (Y + N / u)) * u * E₁),
    Real.sq_sqrt (by positivity : 0 ≤ 2 * (F * (Y + N / v)) * v * E₂),
    Real.sq_sqrt (mul_nonneg hu.le hv.le), Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sq_sqrt hE₁, Real.sq_sqrt hE₂]
  ring

/-- The divisor-product upper cutoff gives one budget independent of the
chosen two divisor blocks. The lower cutoff controls the geometry. -/
theorem quadratic_growth_band_root_bound {F Y N u v D E₁ E₂ : ℝ}
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hN : 0 ≤ N)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hD : 0 < D)
    (hP : u * v ≤ 2 * D) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) :
    Real.sqrt (2 * (F * (Y + N / u)) * u * E₁) *
      Real.sqrt (2 * (F * (Y + N / v)) * v * E₂) ≤
      8 * F * Real.sqrt D *
        (Y + Real.sqrt (Y * N) + N / Real.sqrt D) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have hv₀ : 0 < v := zero_lt_one.trans_le hv
  have hsp : Real.sqrt (u * v) ≤ 2 * Real.sqrt D := by
    have hh : u * v ≤ 4 * D := by linarith
    calc
      _ ≤ Real.sqrt (4 * D) := Real.sqrt_le_sqrt hh
      _ = 2 * Real.sqrt D := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have hsd : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  have hsu : Real.sqrt (u * v) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hu₀ hv₀)).ne'
  have hp := quadratic_two_scale_sqrt_cost hY hN hu hv
  rw [root_product_factor hF hY hN hu₀ hv₀ hE₁ hE₂]
  calc
    _ ≤ 2 * F * Real.sqrt (u * v) *
        (Y + 2 * Real.sqrt (Y * N) + N / Real.sqrt (u * v)) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by gcongr
    _ ≤ 8 * F * Real.sqrt D *
        (Y + Real.sqrt (Y * N) + N / Real.sqrt D) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hy := mul_le_mul_of_nonneg_right hsp hY
      have hc := mul_le_mul_of_nonneg_right hsp (Real.sqrt_nonneg (Y * N))
      have hn := hN
      have hid₁ : Real.sqrt (u * v) * (N / Real.sqrt (u * v)) = N := by field_simp
      have hid₂ : Real.sqrt D * (N / Real.sqrt D) = N := by field_simp
      have hh : Real.sqrt (u * v) *
          (Y + 2 * Real.sqrt (Y * N) + N / Real.sqrt (u * v)) ≤
          4 * Real.sqrt D * (Y + Real.sqrt (Y * N) + N / Real.sqrt D) := by
        rw [mul_add, mul_add, hid₁]
        rw [mul_add, mul_add]
        nlinarith [mul_nonneg (Real.sqrt_nonneg D) hY]
      nlinarith [mul_le_mul_of_nonneg_left hh hF]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthBandBalance
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common band budget has the required low/high recursive size -/

namespace Ostmann

theorem quadratic_growth_band_budget_nonneg {F Y N D E : ℝ}
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hN : 0 ≤ N) (_hD : 0 ≤ D) (hE : 0 ≤ E) :
    0 ≤ quadraticGrowthBandBudget F Y N D E := by
  unfold quadraticGrowthBandBudget
  positivity

theorem quadratic_second_growth_band_balance {M N B D F Y E A : ℝ}
    (hM : 0 < M) (hN : 0 ≤ N) (hB : 0 < B) (hD : 1 ≤ D)
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / (Real.sqrt B * D) ≤ A) :
    (Real.sqrt M / (Real.sqrt B * D)) * quadraticGrowthBandBudget F Y N D E ≤
      16 * F * (Real.sqrt M / Real.sqrt B * Y + A * N) * E := by
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hsD₀ : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD₀).ne'
  have hid : Real.sqrt M / (Real.sqrt B * D) * Real.sqrt D =
      Real.sqrt M / (Real.sqrt B * Real.sqrt D) := by
    field_simp
    nlinarith only [Real.sq_sqrt hD₀.le]
  have hb := quadratic_small_kernel_envelope hM hN hB hD hY hA hcut
  unfold quadraticGrowthBandBudget
  calc
    _ = (8 * F * E) * ((Real.sqrt M / (Real.sqrt B * D) * Real.sqrt D) *
        (Y + Real.sqrt (Y * N) + N / Real.sqrt D)) := by ring
    _ = (8 * F * E) * ((Real.sqrt M / (Real.sqrt B * Real.sqrt D)) *
        (Y + Real.sqrt (Y * N) + N / Real.sqrt D)) := by rw [hid]
    _ ≤ (8 * F * E) * (2 * (Real.sqrt M / Real.sqrt B * Y + A * N)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGrowthDivisorBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual shorter sieve matrices supply every divisor-band budget -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_growth_cutoff_bounds {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B N : ℕ, 0 < B → 0 < N →
      ∀ i ≤ Nat.log 2 N,
        QuadraticSieveBound B (N / 2 ^ i) (quadraticGrowthCutoff C ε ξ B N i) := by
  obtain ⟨C, hC, hc⟩ := quadratic_growth_shortened_transpose h ε hε
  refine ⟨C, hC, ?_⟩
  intro B N hB hN i hi
  apply hc B N (2 ^ i) hB (by exact one_le_pow₀ (by norm_num))
  exact (Nat.pow_le_pow_right (by norm_num) hi).trans
    (Nat.pow_log_le_self 2 hN.ne')

theorem quadratic_growth_cutoff_nonneg {C ε ξ : ℝ} (hC : 0 ≤ C) (B N i : ℕ) :
    0 ≤ quadraticGrowthCutoff C ε ξ B N i := by
  unfold quadraticGrowthCutoff
  positivity

theorem quadratic_growth_divisor_budget_nonneg {C ε ξ : ℝ} (hC : 0 ≤ C)
    (B N D : ℕ) (v w : ℕ → ℂ) :
    0 ≤ quadraticGrowthDivisorBudget C ε ξ B N D v w := by
  unfold quadraticGrowthDivisorBudget
  exact quadratic_growth_band_budget_nonneg (by positivity) (by positivity)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity)

theorem quadratic_growth_cutoff_cost {C ε ξ : ℝ} (hC : 0 ≤ C)
    {B N D : ℕ} (hD : 0 < D) (v w : ℕ → ℂ)
    {i j : ℕ} (hP : 2 ^ i * 2 ^ j ≤ 2 * D) :
    Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N i * (2 ^ i : ℕ) *
        quadraticDivisorMoment N v) *
      Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N j * (2 ^ j : ℕ) *
        quadraticDivisorMoment N w) ≤
      quadraticGrowthDivisorBudget C ε ξ B N D v w := by
  apply quadratic_growth_band_root_bound (by positivity) (by positivity) (Nat.cast_nonneg N)
    (by exact_mod_cast (show 1 ≤ (2 : ℕ) ^ i from one_le_pow₀ (by norm_num)))
    (by exact_mod_cast (show 1 ≤ (2 : ℕ) ^ j from one_le_pow₀ (by norm_num)))
    (by exact_mod_cast hD) (by exact_mod_cast hP)
    (Finset.sum_nonneg fun _ _ => by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Mobius and square-root weights of the divisor corrections -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_moebius_root_weight {D B d b : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hd : D ≤ d) (hb : B ≤ b) :
    ‖((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)‖ ≤
      1 / ((D : ℝ) * Real.sqrt B) := by
  have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hdr : (D : ℝ) ≤ d := by exact_mod_cast hd
  have hbr : (B : ℝ) ≤ b := by exact_mod_cast hb
  rw [norm_div, norm_div, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (1 / (D : ℝ)) / Real.sqrt B := by
      have hfirst : ‖(ArithmeticFunction.moebius d : ℂ)‖ / (d : ℝ) ≤ 1 / (D : ℝ) :=
        div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1) hμ hDr hdr
      exact div_le_div₀ (div_nonneg (by norm_num) hDr.le)
        hfirst (Real.sqrt_pos.2 hBr) (Real.sqrt_le_sqrt hbr)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pair-to-divisor rearrangement for the retained corrections -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_coprime_divisor_reindex (N : ℕ) (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then ∑ d ∈ (s * t).divisors, F s t d else 0) =
    ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
      ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
  have hlocal (s : ℕ) (hs : s ∈ oddSquarefreeRange (2 * N))
      (t : ℕ) (ht : t ∈ oddSquarefreeRange (2 * N)) :
      (if s.Coprime t then ∑ d ∈ (s * t).divisors, F s t d else 0) =
      ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
        if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
    obtain ⟨hsr, _, hss⟩ := Finset.mem_filter.mp hs
    obtain ⟨htr, _, hst⟩ := Finset.mem_filter.mp ht
    have hq : s * t ≠ 0 := mul_ne_zero hss.ne_zero hst.ne_zero
    have hqtop : s * t ≤ (2 * N) ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul (Finset.mem_Icc.mp hsr).2
        (Finset.mem_Icc.mp htr).2
    have heq : (Finset.Icc 1 ((2 * N) ^ 2)).filter (fun d => d ∣ s * t) = (s * t).divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · intro h
        exact ⟨h.2, hq⟩
      · intro h
        have hd := Nat.mem_divisors.mpr h
        exact ⟨⟨Nat.pos_of_mem_divisors hd,
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) h.1).trans hqtop⟩, h.1⟩
    by_cases hc : s.Coprime t
    · rw [ite_eq_left hc]
      have heq' : (Finset.Icc 1 ((2 * N) ^ 2)).filter
          (fun d => s.Coprime t ∧ d ∣ s * t) = (s * t).divisors := by
        convert heq using 1
        all_goals try with_reducible_and_instances rfl
        ext d
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hc, h.2⟩⟩
      rw [← Finset.sum_filter, heq']
    · simp [hc]
  calc
    _ = ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
          if s.Coprime t ∧ d ∣ s * t then F s t d else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_congr rfl (fun t ht => hlocal s hs t ht)
    _ = _ := by
      conv_lhs =>
        arg 2
        ext s
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common cutoffs for the original small-squarefree-kernel block -/

namespace Ostmann

open scoped SchwartzMap BigOperators

theorem quadraticSmallScale_pos {M : ℝ} {b : ℕ} (hM : 0 < M) (hb : 0 < b) :
    0 < quadraticSmallScale M b := by unfold quadraticSmallScale; positivity

theorem quadraticSmallScale_dyadic {M B : ℝ} {b : ℕ}
    (hM : 0 < M) (hB : 0 < B) (hb : B ≤ b) (hb' : (b : ℝ) ≤ 2 * B) :
    Real.sqrt (M / B) / 2 ≤ quadraticSmallScale M b ∧
      quadraticSmallScale M b ≤ 2 * Real.sqrt (M / B) := by
  have hb₀ : 0 < (b : ℝ) := hB.trans_le hb
  have hlo : M / B ≤ 2 * (M / b) := by
    calc
      _ = 2 * (M / (2 * B)) := by ring
      _ ≤ _ := by gcongr
  have hhi : M / b ≤ M / B := div_le_div_of_nonneg_left hM.le hB hb
  have hs₀ := Real.sq_sqrt (div_nonneg hM.le hB.le)
  have hs := Real.sq_sqrt (div_nonneg hM.le hb₀.le)
  have hn₀ := Real.sqrt_nonneg (M / B)
  have hn := Real.sqrt_nonneg (M / b)
  unfold quadraticSmallScale
  constructor <;> nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained small-kernel Fourier window with its actual reciprocal weights -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadraticSmallFourierBound_nonneg (ρ : 𝓢(ℝ, ℂ)) :
    0 ≤ quadraticSmallFourierBound ρ :=
  (norm_nonneg _).trans ((𝓕 (quadraticSmallSquareTest ρ)).norm_le_seminorm ℝ 0)

theorem quadratic_small_window_bound (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) (L : ℕ) :
    ‖quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) X L‖ ≤
      (2 * L + 1) * quadraticSmallFourierBound ρ := by
  have hcard : (Finset.Icc (-(L : ℤ)) L).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  unfold quadraticLatticeWindow
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.Icc (-(L : ℤ)) L, quadraticSmallFourierBound ρ := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n = 0
      · simp only [hn, ite_true, if_true, norm_zero]
        exact quadraticSmallFourierBound_nonneg ρ
      · rw [ite_eq_right hn]
        exact (𝓕 (quadraticSmallSquareTest ρ)).norm_le_seminorm ℝ _
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; push_cast; rfl

theorem quadratic_small_kernel_fourier_weight (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) (L : ℕ)
    {E D B d b : ℕ} (hE : 1 ≤ E) (hD : 0 < D) (hB : 0 < B)
    (hd : D ≤ d) (hb : B ≤ b) :
    ‖(((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) /
        (Real.sqrt b : ℂ)) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) X L‖ ≤
      ((2 * L + 1) * quadraticSmallFourierBound ρ) / ((D : ℝ) * Real.sqrt B) := by
  have hd' : D ≤ E * d := hd.trans (le_mul_of_one_le_left (Nat.zero_le d) hE)
  rw [norm_mul]
  calc
    _ ≤ (1 / ((D : ℝ) * Real.sqrt B)) *
        ((2 * L + 1) * quadraticSmallFourierBound ρ) :=
      mul_le_mul (quadratic_moebius_root_weight hD hB hd' hb)
        (quadratic_small_window_bound ρ X L) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticVariableMatrixBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete variable-cutoff corrections on their actual divisor bands -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_variable_small_high_band (E B N D : ℕ)
    (hE : 1 ≤ E) (hB : 0 < B) (hD : 0 < D)
    (P : ℕ → ℕ → Prop) [DecidableRel P] (v w : ℕ → ℂ) (T : ℝ)
    (hbound : (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) ≤ T) :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then
        (((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
          quadraticDivisorBilinear (2 * N) (2 * N) d v w b else 0‖ ≤
      T / ((D : ℝ) * Real.sqrt B) := by
  let c : ℝ := 1 / ((D : ℝ) * Real.sqrt B)
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        c * ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      split_ifs with h
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (quadratic_moebius_root_weight hD hB
            ((Finset.mem_Ioc.mp hd).1.le.trans (le_mul_of_one_le_left (Nat.zero_le d) hE)) h.1)
          (norm_nonneg _)
      · rw [norm_zero]; dsimp [c]; positivity
    _ = c * (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) := by simp only [Finset.mul_sum]
    _ ≤ c * T := mul_le_mul_of_nonneg_left hbound (by dsimp [c]; positivity)
    _ = _ := by dsimp [c]; ring

theorem quadratic_variable_small_middle_band (ρ : 𝓢(ℝ, ℂ)) (M : ℝ)
    (E B N D L : ℕ) (hE : 1 ≤ E) (hB : 0 < B) (hD : 0 < D)
    (P : ℕ → ℕ → Prop) [DecidableRel P] (v w : ℕ → ℂ) (T : ℝ)
    (hbound : (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) ≤ T) :
    ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ P d b then
        ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
          quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ))
            (quadraticSmallScale M b / (E * d : ℕ)) L) *
          quadraticDivisorBilinear (2 * N) (2 * N) d v w b else 0‖ ≤
      (((2 * L + 1) * quadraticSmallFourierBound ρ) / ((D : ℝ) * Real.sqrt B)) * T := by
  let c : ℝ := ((2 * L + 1) * quadraticSmallFourierBound ρ) / ((D : ℝ) * Real.sqrt B)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (mul_nonneg (by positivity) (quadraticSmallFourierBound_nonneg ρ)) (by positivity)
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        c * ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      split_ifs with h
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (quadratic_small_kernel_fourier_weight ρ _ L hE hD hB
            (Finset.mem_Ioc.mp hd).1.le h.1) (norm_nonneg _)
      · rw [norm_zero]; exact mul_nonneg hc (norm_nonneg _)
    _ = c * (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
        ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) := by simp only [Finset.mul_sum]
    _ ≤ c * T := mul_le_mul_of_nonneg_left hbound hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallCorrectionGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both original small-kernel corrections from the same shorter matrices -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

private theorem matrix_bound {C ε ξ : ℝ} (hC : 0 ≤ C) {B N D : ℕ} (hD : 0 < D)
    (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ b ∈ oddSquarefreeRange (2 * B),
      ‖quadraticDivisorBilinear (2 * N) (2 * N) d v w b‖) ≤
      ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w := by
  have hh := quadratic_bilinear_uniform_bound (2 * B) (2 * N) (2 * N) D v w
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N))
    (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N))
    (quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w)
    (quadratic_growth_divisor_budget_nonneg hC _ _ _ _ _)
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i)
    (fun i _ => quadratic_growth_cutoff_nonneg hC _ _ i) hmat hmat
    (fun _ _ _ _ _ hp => quadratic_growth_cutoff_cost hC hD v w hp)
  simpa only [pow_two, Nat.cast_add, Nat.cast_one] using hh

private theorem weighted_budget {C ε ξ M A : ℝ} (hC : 0 ≤ C)
    {B N D : ℕ} (hM : 0 < M) (hB : 0 < B) (hD : 0 < D) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / (Real.sqrt B * D) ≤ A) (v w : ℕ → ℂ) :
    (Real.sqrt M / (Real.sqrt B * D)) *
        quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w ≤
      16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  have hh := quadratic_second_growth_band_balance hM (show (0 : ℝ) ≤ (2 * N : ℕ) by positivity)
    (show (0 : ℝ) < B by exact_mod_cast hB) (show (1 : ℝ) ≤ D by exact_mod_cast hD)
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) hA hcut
  simpa only [quadraticGrowthDivisorBudget, quadraticSmallCorrectionGrowthScale,
    Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hh

theorem quadratic_small_high_growth {C ε ξ M A : ℝ} (hC : 0 ≤ C)
    {E B N D : ℕ} (hE : 1 ≤ E) (hM : 0 < M) (hB : 0 < B) (hD : 0 < D) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / (Real.sqrt B * D) ≤ A)
    (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallHighBand E B N D P v w‖ ≤
      16 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  classical
  have hl := quadratic_variable_small_high_band E B N D hE hB hD P v w _
    (matrix_bound hC hD v w hmat)
  change ‖quadraticSmallHighBand E B N D P v w‖ ≤ _ at hl
  have hb := weighted_budget (ε := ε) (ξ := ξ) (N := N) hC hM hB hD hA hcut v w
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg M)]
  apply (mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg M)).trans
  calc
    _ = ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        ((Real.sqrt M / (Real.sqrt B * D)) * quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w) := by ring
    _ ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        (16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

theorem quadratic_small_middle_growth (ρ : 𝓢(ℝ, ℂ))
    {C ε ξ M A : ℝ} (hC : 0 ≤ C)
    {E B N D L : ℕ} (hE : 1 ≤ E) (hM : 0 < M) (hB : 0 < B) (hD : 0 < D) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / (Real.sqrt B * D) ≤ A)
    (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallMiddleBand ρ M E B N D L P v w‖ ≤
      16 * (2 * L + 1) * quadraticSmallFourierBound ρ *
        ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  classical
  have hl := quadratic_variable_small_middle_band ρ M E B N D L hE hB hD P v w _
    (matrix_bound hC hD v w hmat)
  change ‖quadraticSmallMiddleBand ρ M E B N D L P v w‖ ≤ _ at hl
  have hb := weighted_budget (ε := ε) (ξ := ξ) (N := N) hC hM hB hD hA hcut v w
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg M)]
  apply (mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg M)).trans
  calc
    _ = ((2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        ((Real.sqrt M / (Real.sqrt B * D)) * quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) D v w) := by ring
    _ ≤ ((2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2) *
        (16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg (by positivity)
        (quadraticSmallFourierBound_nonneg ρ)) (sq_nonneg _))
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform current-exponent bound over all frequency blocks -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_frequency_root_power {ξ : ℝ} {B K : ℕ}
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hB : 0 < B) (hBK : B ≤ K) :
    (((2 * B : ℕ) : ℝ) ^ ξ) / Real.sqrt B ≤ 4 * (K : ℝ) ^ (ξ - 1 / 2) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow := Real.rpow_le_rpow hBr.le (show (B : ℝ) ≤ K by exact_mod_cast hBK)
    (show 0 ≤ ξ - 1 / 2 by linarith)
  have htwo : (2 : ℝ) ^ ξ ≤ 4 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hξ').trans_eq
    norm_num
  calc
    _ = (2 : ℝ) ^ ξ * (B : ℝ) ^ (ξ - 1 / 2) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) hBr.le,
        Real.rpow_sub hBr, ← Real.sqrt_eq_rpow]
      ring
    _ ≤ _ := mul_le_mul htwo hpow (by positivity) (by norm_num)

theorem quadratic_frequency_power_cost {ε : ℝ} (hε : 0 ≤ ε) {B N K R : ℕ}
    (hBK : B ≤ K) (hNR : N ≤ R) :
    ((((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε) ≤
      (4 * (K : ℝ) * R) ^ ε := by
  apply Real.rpow_le_rpow (by positivity) _ hε
  have hh := mul_le_mul (show (B : ℝ) ≤ K by exact_mod_cast hBK)
    (show (N : ℝ) ≤ R by exact_mod_cast hNR) (Nat.cast_nonneg N) (Nat.cast_nonneg K)
  push_cast
  nlinarith

theorem quadratic_small_growth_uniform {C ε ξ M A : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (_hM : 0 ≤ M) (hA : 0 ≤ A)
    {B N K R : ℕ} (hB : 0 < B) (hBK : B ≤ K) (hNR : N ≤ R)
    (v w : ℕ → ℂ) :
    quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w ≤
      4 * C * (4 * (K : ℝ) * R) ^ ε *
        (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + A * R) *
          (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
            Real.sqrt (quadraticDivisorMoment (2 * N) w)) := by
  have hp := quadratic_frequency_root_power hξ hξ' hB hBK
  have hinner : Real.sqrt M / Real.sqrt B * ((2 * B : ℕ) : ℝ) ^ ξ + A * (2 * N) ≤
      4 * (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + A * R) := by
    calc
      _ = Real.sqrt M * ((((2 * B : ℕ) : ℝ) ^ ξ) / Real.sqrt B) + A * (2 * N) := by ring
      _ ≤ Real.sqrt M * (4 * (K : ℝ) ^ (ξ - 1 / 2)) + A * (2 * R) :=
        add_le_add (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg M)) (by gcongr)
      _ ≤ _ := by nlinarith [mul_nonneg hA (Nat.cast_nonneg R)]
  have hfactor := mul_le_mul_of_nonneg_left (quadratic_frequency_power_cost hε hBK hNR) hC
  unfold quadraticSmallCorrectionGrowthScale
  apply le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hfactor hinner (by positivity) (by positivity)) (by positivity))
  apply le_of_eq
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitDivisor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor-one block, retained separately from positive dyadic intervals -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_unit_divisor_bound (M N₁ N₂ : ℕ) (K₁ K₂ : ℝ)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M N₁ K₁) (h₂ : QuadraticSieveBound M N₂ K₂)
    (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticDivisorBilinear N₁ N₂ 1 a b m‖) ≤
      Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ b) := by
  have hshape : ∀ s ∈ ({1} : Finset ℕ), Squarefree s ∧ Odd s := by
    intro s hs
    have he : s = 1 := Finset.mem_singleton.mp hs
    subst s
    norm_num
  have hcut₁ : ∀ s ∈ ({1} : Finset ℕ), QuadraticSieveBound M (N₁ / s) K₁ := by
    intro s hs
    simpa only [Finset.mem_singleton.mp hs, Nat.div_one] using h₁
  have hcut₂ : ∀ s ∈ ({1} : Finset ℕ), QuadraticSieveBound M (N₂ / s) K₂ := by
    intro s hs
    simpa only [Finset.mem_singleton.mp hs, Nat.div_one] using h₂
  have h := quadratic_divisor_family_bound M N₁ N₂ {1} {1} K₁ K₂
    hK₁ hK₂ hshape hshape hcut₁ hcut₂ a b
  have he (m : ℤ) : quadraticDivisorBilinear N₁ N₂ 1 a b m =
      quadraticCoprimeBilinear N₁ N₂ a b m := by
    simp only [quadraticDivisorBilinear, quadraticCoprimeBilinear, one_dvd, and_true]
  simpa only [he, Finset.sum_singleton, one_dvd, ite_true, if_true,
    Finset.card_singleton, Nat.cast_one, mul_one] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitCorrectionBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Filtered boundary corrections retain the full frequency comparison -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_filtered_unit_bound (B : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (c F : ℕ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hc : ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P b → ‖c b‖ ≤ A) :
    ‖∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then c b * F b else 0‖ ≤
      A * ∑ b ∈ oddSquarefreeRange (2 * B), ‖F b‖ := by
  calc
    _ ≤ ∑ b ∈ oddSquarefreeRange (2 * B), A * ‖F b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      split_ifs with h
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hc b hb h.1 h.2) (norm_nonneg _)
      · rw [norm_zero]
        exact mul_nonneg hA (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticUnitCorrectionGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The missing unit-divisor endpoint has the same normalized growth rate -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_growth_unit_cost {C ε ξ : ℝ} (hC : 0 ≤ C)
    (B N : ℕ) (v w : ℕ → ℂ) :
    Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N 0 * quadraticDivisorMoment N v) *
      Real.sqrt (2 * quadraticGrowthCutoff C ε ξ B N 0 * quadraticDivisorMoment N w) ≤
        quadraticGrowthDivisorBudget C ε ξ B N 1 v w := by
  simpa only [pow_zero, Nat.cast_one, mul_one] using
    quadratic_growth_cutoff_cost hC (show 0 < (1 : ℕ) by decide) v w
      (i := 0) (j := 0) (by norm_num)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallCorrectionGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-kernel divisor cutoff gives the numerical matrix constraint -/

namespace Ostmann

theorem quadratic_small_correction_cutoff {M J : ℝ} {E B b D d : ℕ}
    (hM : 0 < M) (hJ : 1 ≤ J) (hE : 0 < E) (hB : 0 < B) (hD : 0 < D)
    (hb : B ≤ b) (hb' : b ≤ 2 * B) (hd : d ≤ 2 * D)
    (hcut : quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ)) :
    Real.sqrt M / (Real.sqrt B * D) ≤ 8 * E * J := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hbR : (B : ℝ) ≤ b := by exact_mod_cast hb
  have hbR' : (b : ℝ) ≤ 2 * B := by exact_mod_cast hb'
  have hdR : (d : ℝ) ≤ 2 * D := by exact_mod_cast hd
  have hJ₀ : 0 < J := zero_lt_one.trans_le hJ
  have hlo := (quadraticSmallScale_dyadic hM hBR hbR hbR').1
  unfold quadraticSecondLower at hcut
  have hh := (div_lt_iff₀ (show 0 < 2 * J by positivity)).mp hcut
  have hed : ((E * d : ℕ) : ℝ) ≤ (E : ℝ) * (2 * D) := by
    push_cast
    exact mul_le_mul_of_nonneg_left hdR hER.le
  have heJ := mul_le_mul_of_nonneg_right hed (show 0 ≤ 2 * J by positivity)
  have hs : Real.sqrt (M / B) ≤ 8 * E * J * D := by nlinarith
  rw [Real.sqrt_div hM.le] at hs
  have hfin : (Real.sqrt M / Real.sqrt B) / D ≤ 8 * E * J :=
    (div_le_iff₀ hDR).mpr hs
  convert hfin using 1 <;> first | rfl | ring

theorem quadratic_small_high_implies_lower {M J : ℝ} {b E d : ℕ}
    (hM : 0 < M) (hb : 0 < b) (hJ : 1 ≤ J)
    (hcut : quadraticSecondUpper (quadraticSmallScale M b) J < (E * d : ℕ)) :
    quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ) := by
  have hx : 0 ≤ quadraticSmallScale M b := (quadraticSmallScale_pos hM hb).le
  have hJ₀ : 0 < J := zero_lt_one.trans_le hJ
  have hlow : quadraticSecondLower (quadraticSmallScale M b) J ≤ quadraticSmallScale M b := by
    unfold quadraticSecondLower
    exact div_le_self hx (by linarith)
  have hhigh : quadraticSmallScale M b ≤ quadraticSecondUpper (quadraticSmallScale M b) J := by
    unfold quadraticSecondUpper
    nlinarith
  exact hlow.trans_lt (hhigh.trans_lt hcut)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallUnitGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small-kernel corrections at the unit divisor, including its full window -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_small_unit_weighted_growth {C ε ξ M A W : ℝ} (hC : 0 ≤ C)
    {B N : ℕ} (hM : 0 < M) (hB : 0 < B) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hcut : Real.sqrt M / Real.sqrt B ≤ A)
    (P : ℕ → Prop) (c : ℕ → ℂ) (v w : ℕ → ℂ)
    (hc : ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P b → ‖c b‖ ≤ W / Real.sqrt B)
    (hmat : QuadraticSieveBound (2 * B) (2 * N)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0)) :
    ‖(Real.sqrt M : ℂ) * (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
        c b * quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b else 0)‖ ≤
      16 * W * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  classical
  let T := quadraticGrowthDivisorBudget C ε ξ (2 * B) (2 * N) 1 v w
  let K := quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0
  have hK : 0 ≤ K := quadratic_growth_cutoff_nonneg hC _ _ _
  have hroot := quadratic_growth_unit_cost (ε := ε) (ξ := ξ) hC (2 * B) (2 * N) v w
  have hu := (quadratic_unit_divisor_bound (2 * B) (2 * N) (2 * N)
    K K hK hK hmat hmat v w).trans hroot
  have hf := quadratic_filtered_unit_bound B P c
    (fun b => quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b)
    (A := W / Real.sqrt B) (by positivity) hc
  have hl := hf.trans (mul_le_mul_of_nonneg_left hu (show 0 ≤ W / Real.sqrt (B : ℝ) by positivity))
  have hb := quadratic_second_growth_band_balance hM (show (0 : ℝ) ≤ (2 * N : ℕ) by positivity)
    (show (0 : ℝ) < B by exact_mod_cast hB) (by norm_num : (1 : ℝ) ≤ 1)
    (show 0 ≤ C * (((2 * B : ℕ) : ℝ) * (2 * N : ℕ)) ^ ε by positivity)
    (show 0 ≤ ((2 * B : ℕ) : ℝ) ^ ξ by positivity)
    (show 0 ≤ Real.sqrt (quadraticDivisorMoment (2 * N) v) *
      Real.sqrt (quadraticDivisorMoment (2 * N) w) by positivity) hA (by simpa using hcut)
  have hb' : (Real.sqrt M / Real.sqrt B) * T ≤
      16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
    simpa only [T, quadraticGrowthDivisorBudget, quadraticSmallCorrectionGrowthScale,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one, mul_assoc] using hb
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg M)]
  apply (mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg M)).trans
  calc
    _ = W * (Real.sqrt M / Real.sqrt B * T) := by ring
    _ ≤ W * (16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w) :=
      mul_le_mul_of_nonneg_left hb' hW
    _ = _ := by ring

theorem quadratic_small_high_unit_growth {C ε ξ M A : ℝ} (hC : 0 ≤ C)
    {E B N : ℕ} (hE : 1 ≤ E) (hM : 0 < M) (hB : 0 < B) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / Real.sqrt B ≤ A)
    (P : ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : QuadraticSieveBound (2 * B) (2 * N)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0)) :
    ‖(Real.sqrt M : ℂ) * (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
        (((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
          quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b else 0)‖ ≤
      16 * quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  simpa only [mul_one] using quadratic_small_unit_weighted_growth hC hM hB hA
    (by norm_num : (0 : ℝ) ≤ 1) hcut P _ v w
    (fun b _ hb _ => by simpa only [Nat.cast_one, one_mul] using
      quadratic_moebius_root_weight (show 0 < (1 : ℕ) by decide) hB hE hb) hmat

theorem quadratic_small_middle_unit_growth (ρ : 𝓢(ℝ, ℂ))
    {C ε ξ M A : ℝ} (hC : 0 ≤ C)
    {E B N L : ℕ} (hE : 1 ≤ E) (hM : 0 < M) (hB : 0 < B) (hA : 0 ≤ A)
    (hcut : Real.sqrt M / Real.sqrt B ≤ A)
    (P : ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : QuadraticSieveBound (2 * B) (2 * N)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) 0)) :
    ‖(Real.sqrt M : ℂ) * (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P b then
        ((((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
          quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (quadraticSmallScale M b / E) L) *
          quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b else 0)‖ ≤
      16 * (2 * L + 1) * quadraticSmallFourierBound ρ *
        quadraticSmallCorrectionGrowthScale C ε ξ M A B N v w := by
  have hW : 0 ≤ (2 * L + 1 : ℝ) * quadraticSmallFourierBound ρ :=
    mul_nonneg (by positivity) (quadraticSmallFourierBound_nonneg ρ)
  let c : ℕ → ℂ := fun b =>
    (((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
      quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (quadraticSmallScale M b / E) L
  have hc : ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P b →
      ‖c b‖ ≤ ((2 * L + 1) * quadraticSmallFourierBound ρ) / Real.sqrt B := by
    intro b _ hb _
    simpa only [c, mul_one, Nat.cast_one, one_mul] using
      quadratic_small_kernel_fourier_weight ρ (quadraticSmallScale M b / E) L
        (E := E) (D := 1) (d := 1) hE (by decide) hB le_rfl hb
  have hh := quadratic_small_unit_weighted_growth hC hM hB hA hW hcut P c v w hc hmat
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWholeSmallHighGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete small-kernel high-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_whole_small_high_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {E B N Q : ℕ} (hM : 0 < M) (hE : 1 ≤ E) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hP : ∀ d ∈ Finset.Icc 1 Q, ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P d b →
      quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ))
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallHighTotal E B N Q P v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (16 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticSmallCorrectionGrowthScale C ε ξ M (8 * E * J) B N v w) := by
  classical
  let S := quadraticSmallCorrectionGrowthScale C ε ξ M (8 * E * J) B N v w
  let V := 16 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * S
  let F := fun d => (Real.sqrt M : ℂ) *
    ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticDivisorBilinear (2 * N) (2 * N) d
          v w b else 0
  have hS : 0 ≤ S := by dsimp [S, quadraticSmallCorrectionGrowthScale]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlog : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    nlinarith
  have hunit : ‖F 1‖ ≤ V := by
    by_cases hc : Real.sqrt M / Real.sqrt B ≤ 8 * E * J
    · have hu := quadratic_small_high_unit_growth hC hE hM hB (by positivity) hc (P 1) v w
        (by simpa only [pow_zero, Nat.div_one] using hmat 0 (Nat.zero_le _))
      have heq : F 1 = (Real.sqrt M : ℂ) * (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
          (((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
            quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b else 0) := by
        simp only [F, mul_one]
      rw [heq]
      apply hu.trans
      change 16 * S ≤ V
      dsimp [V]
      nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 16 * S by positivity)]
    · have hz : F 1 = 0 := by
        dsimp [F]
        have hh : (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
            (((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
              quadraticDivisorBilinear (2 * N) (2 * N) 1
                v w b else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          have hn : ¬ (B ≤ b ∧ P 1 b) := by
            intro h
            apply hc
            have hbound := quadratic_small_correction_cutoff (D := 1) (d := 1)
              hM hJ (by omega : 0 < E) hB (by decide) h.1
              (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2 (by norm_num)
              (hP 1 (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩) b hb h.1 h.2)
            simpa only [Nat.cast_one, mul_one] using hbound
          simp only [hn, ite_false, if_false]
        simp only [mul_one]
        rw [hh, mul_zero]
      rw [hz, norm_zero]
      exact hV
  have hblock (j : ℕ) (_hj : j < Nat.log 2 Q + 1) :
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ V := by
    let D := 2 ^ j
    let P' := fun d b => d ≤ Q ∧ P d b
    have heq : (∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0) =
        (Real.sqrt M : ℂ) * quadraticSmallHighBand E B N D P' v w := by
      simp only [quadraticSmallHighBand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [F, P']
      by_cases hd : d ≤ Q
      · simp only [hd, ite_true, if_true, true_and, Finset.mul_sum]
      · simp only [hd, ite_false, if_false, false_and, and_false, Finset.sum_const_zero, mul_zero]
    change ‖∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0‖ ≤ V
    rw [heq]
    by_cases hc : Real.sqrt M / (Real.sqrt B * D) ≤ 8 * E * J
    · exact quadratic_small_high_growth hC hE hM hB (by dsimp [D]; positivity)
        (by positivity) hc P' v w hmat
    · have hz : quadraticSmallHighBand E B N D P' v w = 0 := by
        unfold quadraticSmallHighBand
        apply Finset.sum_eq_zero
        intro d hd
        apply Finset.sum_eq_zero
        intro b hb
        have hn : ¬ (B ≤ b ∧ P' d b) := by
          intro h
          have hdp := (Finset.mem_Ioc.mp hd).1
          apply hc
          exact quadratic_small_correction_cutoff hM hJ (by omega : 0 < E)
            hB (by dsimp [D]; positivity) h.1
            (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
            (Finset.mem_Ioc.mp hd).2
            (hP d (Finset.mem_Icc.mpr
              ⟨Nat.succ_le_of_lt ((Nat.zero_le D).trans_lt hdp), h.2.1⟩) b hb h.1 h.2.2)
        simp only [hn, ite_false, if_false]
      rw [hz, mul_zero, norm_zero]
      exact hV
  have hb := quadratic_correction_divisor_bound hQ F V (fun _ => V) hunit hblock
  have heq : (∑ d ∈ Finset.Icc 1 Q, F d) =
      (Real.sqrt M : ℂ) * quadraticSmallHighTotal E B N Q P v w := by
    simp only [F, quadraticSmallHighTotal, Finset.mul_sum]
  rw [heq] at hb
  apply hb.trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [V, S]
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticWholeSmallMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete small-kernel middle-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_whole_small_middle_growth (ρ : 𝓢(ℝ, ℂ)) {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {E B N Q L : ℕ} (hM : 0 < M) (hE : 1 ≤ E) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hP : ∀ d ∈ Finset.Icc 1 Q, ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P d b →
      quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ))
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallMiddleTotal ρ M E B N Q L P v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (16 * (2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticSmallCorrectionGrowthScale C ε ξ M (8 * E * J) B N v w) := by
  classical
  let S := quadraticSmallCorrectionGrowthScale C ε ξ M (8 * E * J) B N v w
  let V := 16 * (2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * S
  let F := fun d => (Real.sqrt M : ℂ) *
    ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P d b then
      ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ))
          (quadraticSmallScale M b / (E * d : ℕ)) L) *
        quadraticDivisorBilinear (2 * N) (2 * N) d
          v w b else 0
  have hρ := quadraticSmallFourierBound_nonneg ρ
  have hS : 0 ≤ S := by dsimp [S, quadraticSmallCorrectionGrowthScale]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlog : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    nlinarith
  have hunit : ‖F 1‖ ≤ V := by
    by_cases hc : Real.sqrt M / Real.sqrt B ≤ 8 * E * J
    · have hu := quadratic_small_middle_unit_growth ρ (L := L) hC hE hM hB (by positivity) hc (P 1) v w
        (by simpa only [pow_zero, Nat.div_one] using hmat 0 (Nat.zero_le _))
      have heq : F 1 = (Real.sqrt M : ℂ) * (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
          ((((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
            quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (quadraticSmallScale M b / E) L) *
            quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b else 0) := by
        simp only [F, mul_one]
      rw [heq]
      apply hu.trans
      change 16 * (2 * L + 1) * quadraticSmallFourierBound ρ * S ≤ V
      dsimp [V]
      nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 16 * (2 * L + 1) * quadraticSmallFourierBound ρ * S by positivity)]
    · have hz : F 1 = 0 := by
        dsimp [F]
        have hh : (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
            ((((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
            quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (quadraticSmallScale M b / E) L) *
              quadraticDivisorBilinear (2 * N) (2 * N) 1
                v w b else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          have hn : ¬ (B ≤ b ∧ P 1 b) := by
            intro h
            apply hc
            have hbound := quadratic_small_correction_cutoff (D := 1) (d := 1)
              hM hJ (by omega : 0 < E) hB (by decide) h.1
              (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2 (by norm_num)
              (hP 1 (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩) b hb h.1 h.2)
            simpa only [Nat.cast_one, mul_one] using hbound
          simp only [hn, ite_false, if_false]
        simp only [mul_one]
        rw [hh, mul_zero]
      rw [hz, norm_zero]
      exact hV
  have hblock (j : ℕ) (_hj : j < Nat.log 2 Q + 1) :
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ V := by
    let D := 2 ^ j
    let P' := fun d b => d ≤ Q ∧ P d b
    have heq : (∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0) =
        (Real.sqrt M : ℂ) * quadraticSmallMiddleBand ρ M E B N D L P' v w := by
      simp only [quadraticSmallMiddleBand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [F, P']
      by_cases hd : d ≤ Q
      · simp only [hd, ite_true, if_true, true_and, Finset.mul_sum]
      · simp only [hd, ite_false, if_false, false_and, and_false, Finset.sum_const_zero, mul_zero]
    change ‖∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0‖ ≤ V
    rw [heq]
    by_cases hc : Real.sqrt M / (Real.sqrt B * D) ≤ 8 * E * J
    · exact quadratic_small_middle_growth ρ hC hE hM hB (by dsimp [D]; positivity)
        (by positivity) hc P' v w hmat
    · have hz : quadraticSmallMiddleBand ρ M E B N D L P' v w = 0 := by
        unfold quadraticSmallMiddleBand
        apply Finset.sum_eq_zero
        intro d hd
        apply Finset.sum_eq_zero
        intro b hb
        have hn : ¬ (B ≤ b ∧ P' d b) := by
          intro h
          have hdp := (Finset.mem_Ioc.mp hd).1
          apply hc
          exact quadratic_small_correction_cutoff hM hJ (by omega : 0 < E)
            hB (by dsimp [D]; positivity) h.1
            (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
            (Finset.mem_Ioc.mp hd).2
            (hP d (Finset.mem_Icc.mpr
              ⟨Nat.succ_le_of_lt ((Nat.zero_le D).trans_lt hdp), h.2.1⟩) b hb h.1 h.2.2)
        simp only [hn, ite_false, if_false]
      rw [hz, mul_zero, norm_zero]
      exact hV
  have hb := quadratic_correction_divisor_bound hQ F V (fun _ => V) hunit hblock
  have heq : (∑ d ∈ Finset.Icc 1 Q, F d) =
      (Real.sqrt M : ℂ) * quadraticSmallMiddleTotal ρ M E B N Q L P v w := by
    simp only [F, quadraticSmallMiddleTotal, Finset.mul_sum]
  rw [heq] at hb
  apply hb.trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [V, S]
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticOriginalMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every full correction uses its original frequency-dependent cutoff -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_whole_original_small_high_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {E B N Q : ℕ} (hM : 0 < M) (hE : 1 ≤ E) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallHighTotal E B N Q
        (fun d b => R d b ∧ quadraticSecondUpper (quadraticSmallScale M b) J < (E * d : ℕ)) v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (16 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticSmallCorrectionGrowthScale C ε ξ M (8 * E * J) B N v w) := by
  apply quadratic_whole_small_high_growth hC hM hE hB hN hQ hJ _ v w _ hmat
  intro d _ b hb _ hp
  exact quadratic_small_high_implies_lower hM
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1 hJ hp.2

theorem quadratic_whole_original_small_middle_growth (ρ : 𝓢(ℝ, ℂ))
    {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {E B N Q L : ℕ} (hM : 0 < M) (hE : 1 ≤ E) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallMiddleTotal ρ M E B N Q L
        (fun d b => R d b ∧ quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ) ∧
          (E * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J) v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (16 * (2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticSmallCorrectionGrowthScale C ε ξ M (8 * E * J) B N v w) := by
  apply quadratic_whole_small_middle_growth ρ hC hM hE hB hN hQ hJ _ v w _ hmat
  intro d _ b _ _ hp
  exact hp.2.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the actual gcd from the quadratic pair family -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_gcd_pair_reindex {N D : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (F : ℕ → ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N D, F z.1 z.2) =
      ∑ z ∈ quadraticGcdPairs (N / D) 1,
        if D.Coprime z.1 ∧ D.Coprime z.2 then F (D * z.1) (D * z.2) else 0 := by
  let P := (quadraticGcdPairs (N / D) 1).filter
    (fun z => D.Coprime z.1 ∧ D.Coprime z.2)
  have hsum : (∑ z ∈ P, F (D * z.1) (D * z.2)) =
      ∑ z ∈ quadraticGcdPairs (N / D) 1,
        if D.Coprime z.1 ∧ D.Coprime z.2 then F (D * z.1) (D * z.2) else 0 := by
    exact Finset.sum_filter _ _
  rw [← hsum]
  symm
  apply Finset.sum_bij (fun z _ => (D * z.1, D * z.2))
  · intro z hz
    obtain ⟨hz, hcop⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨
      (mem_oddSquarefreeRange_mul hD hDo).mpr ⟨h₁, hcop.1⟩,
      (mem_oddSquarefreeRange_mul hD hDo).mpr ⟨h₂, hcop.2⟩⟩, ?_⟩
    simp only [Nat.gcd_mul_left, hg, mul_one]
  · intro z _ y _ heq
    apply Prod.ext
    · have hh := congrArg Prod.fst heq
      exact mul_left_cancel₀ hD.ne_zero hh
    · have hh := congrArg Prod.snd heq
      exact mul_left_cancel₀ hD.ne_zero hh
  · intro z hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
    have hd₁ : D ∣ z.1 := hg ▸ Nat.gcd_dvd_left z.1 z.2
    have hd₂ : D ∣ z.2 := hg ▸ Nat.gcd_dvd_right z.1 z.2
    have he₁ : D * (z.1 / D) = z.1 := Nat.mul_div_cancel' hd₁
    have he₂ : D * (z.2 / D) = z.2 := Nat.mul_div_cancel' hd₂
    have hr₁ := (mem_oddSquarefreeRange_mul hD hDo).mp (he₁ ▸ h₁)
    have hr₂ := (mem_oddSquarefreeRange_mul hD hDo).mp (he₂ ▸ h₂)
    refine ⟨(z.1 / D, z.2 / D), ?_, Prod.ext he₁ he₂⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr₁.1, hr₂.1⟩, ?_⟩,
      hr₁.2, hr₂.2⟩
    have hc := Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_left z.2 (Finset.mem_Icc.mp (Finset.mem_filter.mp h₁).1).1)
    rwa [hg] at hc
  · intro _ _
    rfl

 theorem quadraticPairKernel_mul_coprime {D a b : ℕ} (hD : D ≠ 0)
    (hab : a.Coprime b) : quadraticPairKernel (D * a) (D * b) = a * b := by
  have hg : (D * a).gcd (D * b) = D := by simp [Nat.gcd_mul_left, hab.gcd_eq_one]
  rw [quadraticPairKernel, hg]
  simp only [Nat.mul_div_right _ (Nat.pos_of_ne_zero hD)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdCoefficientBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual gcd-removal coefficients for all three divisor corrections -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_coefficient_reindex {N D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N D,
      v z.1 * conj (w z.2) * F (quadraticPairKernel z.1 z.2)) =
    ∑ z ∈ quadraticGcdPairs (N / D) 1,
      quadraticDivisibilityCoeff D v z.1 * conj (quadraticDivisibilityCoeff D w z.2) * F (z.1 * z.2) := by
  rw [quadratic_gcd_pair_reindex (N := N) hD ho
    (fun s t => v s * conj (w t) * F (quadraticPairKernel s t))]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨_, hg⟩ := Finset.mem_filter.mp hz
  rw [quadraticPairKernel_mul_coprime hD.ne_zero hg]
  unfold quadraticDivisibilityCoeff
  by_cases hs : D.Coprime z.1
  · by_cases ht : D.Coprime z.2
    · rw [ite_eq_left ⟨hs, ht⟩, ite_eq_left hs, ite_eq_left ht]
    · rw [ite_eq_right (fun h => ht h.2), ite_eq_left hs, ite_eq_right ht]
      simp
  · rw [ite_eq_right (fun h => hs h.1), ite_eq_right hs]
    simp

theorem quadratic_gcd_coefficient_energy {N D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v : ℕ → ℂ) :
    quadraticSieveEnergy (N / D) (quadraticDivisibilityCoeff D v) ≤ quadraticSieveEnergy N v := by
  rw [quadraticSieveEnergy_divisibility D N hD ho]
  apply Finset.sum_le_sum
  intro n _
  dsimp only
  split_ifs
  · rfl
  · simp

theorem quadratic_coprime_kernel_sum (N : ℕ) (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N 1, v z.1 * conj (w z.2) * F (z.1 * z.2)) =
      ∑ s ∈ oddSquarefreeRange N, ∑ t ∈ oddSquarefreeRange N,
        if s.Coprime t then v s * conj (w t) * F (s * t) else 0 := by
  unfold quadraticGcdPairs
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdRangeBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A genuine dyadic range after removing the common divisor -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_pair_range_extension {L U : ℕ} (hLU : L ≤ U)
    (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs U 1,
      quadraticRangeCoeff L v z.1 * conj (quadraticRangeCoeff L w z.2) * F (z.1 * z.2)) =
      ∑ z ∈ quadraticGcdPairs L 1, v z.1 * conj (w z.2) * F (z.1 * z.2) := by
  have hsub : quadraticGcdPairs L 1 ⊆ quadraticGcdPairs U 1 := by
    intro z hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨oddSquarefreeRange_mono hLU hs, oddSquarefreeRange_mono hLU ht⟩, hg⟩
  have hz (z : ℕ × ℕ) (hu : z ∈ quadraticGcdPairs U 1) (hl : z ∉ quadraticGcdPairs L 1) :
      quadraticRangeCoeff L v z.1 * conj (quadraticRangeCoeff L w z.2) * F (z.1 * z.2) = 0 := by
    obtain ⟨hu, hg⟩ := Finset.mem_filter.mp hu
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hu
    by_cases h₁ : z.1 ≤ L
    · have h₂ : ¬ z.2 ≤ L := by
        intro h₂
        apply hl
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hg⟩
        · obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hs
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, h₁⟩, ho, hsf⟩
        · obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp ht
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, h₂⟩, ho, hsf⟩
      simp [quadraticRangeCoeff, h₂]
    · simp [quadraticRangeCoeff, h₁]
  rw [← Finset.sum_subset hsub hz]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have h₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
  have h₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).2
  simp [quadraticRangeCoeff, h₁, h₂]

theorem quadratic_gcd_block_range (R D : ℕ) :
    (2 * R) / D ≤ 2 * quadraticGcdBlockSize R D := by
  have h₁ : (((2 * R) / D : ℕ) : ℝ) ≤ (2 * (R : ℝ)) / D := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_div_le (m := 2 * R) (n := D) (α := ℝ))
  have h₂ : (R : ℝ) / D ≤ (quadraticGcdBlockSize R D : ℝ) := Nat.le_ceil _
  have hh : (((2 * R) / D : ℕ) : ℝ) ≤ 2 * (quadraticGcdBlockSize R D : ℝ) := by
    rw [mul_div_assoc] at h₁
    linarith
  exact_mod_cast hh

theorem quadratic_gcd_block_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) * F (quadraticPairKernel z.1 z.2)) =
      ∑ z ∈ quadraticGcdPairs (2 * quadraticGcdBlockSize R D) 1,
        quadraticGcdBlockCoeff R D v z.1 * conj (quadraticGcdBlockCoeff R D w z.2) * F (z.1 * z.2) := by
  rw [quadratic_gcd_coefficient_reindex hD ho]
  exact (quadratic_gcd_pair_range_extension (quadratic_gcd_block_range R D)
    (quadraticDivisibilityCoeff D v) (quadraticDivisibilityCoeff D w) F).symm

theorem quadratic_range_energy {L U : ℕ} (hLU : L ≤ U) (v : ℕ → ℂ) :
    quadraticSieveEnergy U (quadraticRangeCoeff L v) = quadraticSieveEnergy L v := by
  unfold quadraticSieveEnergy
  have he : (∑ n ∈ oddSquarefreeRange L, ‖quadraticRangeCoeff L v n‖ ^ 2) =
      ∑ n ∈ oddSquarefreeRange U, ‖quadraticRangeCoeff L v n‖ ^ 2 := by
    apply Finset.sum_subset (oddSquarefreeRange_mono hLU)
    intro n hn hnL
    have hnl : ¬ n ≤ L := by
      intro hh
      apply hnL
      obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, hh⟩, ho, hsf⟩
    simp [quadraticRangeCoeff, hnl]
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  simp [quadraticRangeCoeff, (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2]

theorem quadratic_gcd_block_energy {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v : ℕ → ℂ) :
    quadraticSieveEnergy (2 * quadraticGcdBlockSize R D) (quadraticGcdBlockCoeff R D v) ≤
      quadraticSieveEnergy (2 * R) v := by
  unfold quadraticGcdBlockCoeff
  rw [quadratic_range_energy (quadratic_gcd_block_range R D)]
  exact quadratic_gcd_coefficient_energy hD ho v

theorem quadraticGcdBlockSize_pos {R D : ℕ} (hR : 0 < R) (hD : 0 < D) :
    0 < quadraticGcdBlockSize R D := by
  apply Nat.ceil_pos.mpr
  exact div_pos (by exact_mod_cast hR) (by exact_mod_cast hD)

theorem quadraticGcdBlockSize_le {R D : ℕ} (hD : 0 < D) :
    quadraticGcdBlockSize R D ≤ R := by
  apply Nat.ceil_le.mpr
  exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hD)

theorem quadratic_gcd_block_divisor_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R D : ℕ, Squarefree D → Odd D → ∀ v : ℕ → ℂ,
      quadraticDivisorMoment (2 * quadraticGcdBlockSize R D) (quadraticGcdBlockCoeff R D v) ≤
        C * (2 * (R : ℝ)) ^ ε * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_moment_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro R D hD ho v
  apply (hc _ _).trans
  have hsize : (2 * quadraticGcdBlockSize R D : ℝ) ≤ 2 * R := by
    exact_mod_cast Nat.mul_le_mul_left 2 (quadraticGcdBlockSize_le (Nat.pos_of_ne_zero hD.ne_zero))
  have hpow := Real.rpow_le_rpow (by positivity) hsize hε.le
  have henergy := quadratic_gcd_block_energy (R := R) hD ho v
  have hn : 0 ≤ quadraticSieveEnergy (2 * quadraticGcdBlockSize R D) (quadraticGcdBlockCoeff R D v) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC.le) henergy hn (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The correction envelope uses only the original coefficient energy -/

namespace Ostmann

theorem quadraticCorrectionScalar_nonneg {C ε ξ M J : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hJ : 0 ≤ J) (N Q K L : ℕ) :
    0 ≤ quadraticCorrectionScalar C ε ξ M J N Q K L := by
  unfold quadraticCorrectionScalar
  positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDyadicCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit dyadic-bin count costs only an arbitrarily small power -/

namespace Ostmann

 theorem quadratic_dyadic_count_bound (ε : ℝ) (hε : 0 < ε) (N : ℕ) (hN : 1 ≤ N) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤
      (1 + (ε * Real.log 2)⁻¹) * (N : ℝ) ^ ε := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (1 : ℝ) ≤ (N : ℝ) ^ ε :=
    Real.one_le_rpow (by exact_mod_cast hN) hε.le
  have hb := Real.natLog_le_logb N 2
  change (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 at hb
  calc
    _ = (Nat.log 2 N : ℝ) + 1 := by push_cast; rfl
    _ ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ ((N : ℝ) ^ ε / ε) / Real.log 2 + (N : ℝ) ^ ε :=
      add_le_add (div_le_div_of_nonneg_right (Real.log_natCast_le_rpow_div N hε) hl.le) hp
    _ = _ := by field_simp; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullSmallHighGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire original small-kernel high correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_full_small_high_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) {E N Q K : ℕ}
    (hM : 0 < M) (hE : 1 ≤ E)
    (hN : 0 < N) (hQ : 1 ≤ Q) (hK : 0 < K) (hJ : 1 ≤ J)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
      QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticFullSmallHighCorrection M J E N Q K R v w‖ ≤
      ((Nat.log 2 K + 1 : ℕ) : ℝ) * (((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (16 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          (4 * C * (4 * (K : ℝ) * N) ^ ε *
            (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + (8 * E * J) * N) *
              (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
                Real.sqrt (quadraticDivisorMoment (2 * N) w))))) := by
  classical
  apply quadratic_correction_frequency_bound
  intro i hi
  let B := 2 ^ i
  have hB : 0 < B := by dsimp [B]; positivity
  have hBK : B ≤ K := quadratic_frequency_block_le hK hi
  let R' := fun d b => b ≤ K ∧ b < 2 * B ∧ R d b
  have heq : (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ b ≤ K ∧ b < 2 * B then
        (if R d b ∧ quadraticSecondUpper (quadraticSmallScale M b) J < (E * d : ℕ) then
          (((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) * quadraticDivisorBilinear (2 * N) (2 * N) d
            v w b else 0) else 0) =
      quadraticSmallHighTotal E B N Q
        (fun d b => R' d b ∧ quadraticSecondUpper (quadraticSmallScale M b) J < (E * d : ℕ)) v w := by
    unfold quadraticSmallHighTotal
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [R']
    by_cases h₁ : B ≤ b <;> by_cases h₂ : b ≤ K <;> by_cases h₃ : b < 2 * B <;>
      simp [h₁, h₂, h₃]
  change ‖(Real.sqrt M : ℂ) * _‖ ≤ _
  rw [heq]
  apply (quadratic_whole_original_small_high_growth hC hM hE hB hN hQ hJ R' v w
    (hmat B hB hBK)).trans
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (quadratic_small_growth_uniform hC hε hξ hξ' hM.le (by positivity) hB hBK le_rfl v w)
      (show 0 ≤ 16 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 by positivity))
        (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFullSmallMiddleGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire original small-kernel middle correction at the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_full_small_middle_growth (ρ : 𝓢(ℝ, ℂ)) {C ε ξ M J : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) {E N Q K L : ℕ}
    (hM : 0 < M) (hE : 1 ≤ E)
    (hN : 0 < N) (hQ : 1 ≤ Q) (hK : 0 < K) (hJ : 1 ≤ J)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
      QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticFullSmallMiddleCorrection ρ M J E N Q K L R v w‖ ≤
      ((Nat.log 2 K + 1 : ℕ) : ℝ) * (((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (16 * (2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          (4 * C * (4 * (K : ℝ) * N) ^ ε *
            (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + (8 * E * J) * N) *
              (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
                Real.sqrt (quadraticDivisorMoment (2 * N) w))))) := by
  classical
  have hρ := quadraticSmallFourierBound_nonneg ρ
  apply quadratic_correction_frequency_bound
  intro i hi
  let B := 2 ^ i
  have hB : 0 < B := by dsimp [B]; positivity
  have hBK : B ≤ K := quadratic_frequency_block_le hK hi
  let R' := fun d b => b ≤ K ∧ b < 2 * B ∧ R d b
  have heq : (∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
      if B ≤ b ∧ b ≤ K ∧ b < 2 * B then
        (if R d b ∧ quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ) ∧
        (E * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J then
          ((((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (quadraticSmallScale M b / (E * d : ℕ)) L) * quadraticDivisorBilinear (2 * N) (2 * N) d
            v w b else 0) else 0) =
      quadraticSmallMiddleTotal ρ M E B N Q L
        (fun d b => R' d b ∧ quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ) ∧
          (E * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J) v w := by
    unfold quadraticSmallMiddleTotal
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp [R']
    by_cases h₁ : B ≤ b <;> by_cases h₂ : b ≤ K <;> by_cases h₃ : b < 2 * B <;>
      simp [h₁, h₂, h₃]
  change ‖(Real.sqrt M : ℂ) * _‖ ≤ _
  rw [heq]
  apply (quadratic_whole_original_small_middle_growth ρ hC hM hE hB hN hQ hJ R' v w
    (hmat B hB hBK)).trans
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (quadratic_small_growth_uniform hC hε hξ hξ' hM.le (by positivity) hB hBK le_rfl v w)
      (show 0 ≤ 16 * (2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 by positivity))
        (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticExtraDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the fixed conductor factor from the actual small-kernel divisors -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_extra_divisor_reindex (N E : ℕ) (hE : 0 < E)
    (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then
        if E.Coprime (s * t) then ∑ d ∈ (E * (s * t)).divisors, F s t d else 0
      else 0) =
    ∑ e ∈ E.divisors, ∑ f ∈ Finset.Icc 1 ((2 * N) ^ 2),
      ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t ∧ f ∣ s * t then
          if E.Coprime (s * t) then F s t (e * f) else 0
        else 0 := by
  have hlocal (s : ℕ) (hs : s ∈ oddSquarefreeRange (2 * N))
      (t : ℕ) (ht : t ∈ oddSquarefreeRange (2 * N)) :
      (if s.Coprime t then
        if E.Coprime (s * t) then ∑ d ∈ (E * (s * t)).divisors, F s t d else 0
       else 0) =
      ∑ e ∈ E.divisors, if s.Coprime t then
        ∑ f ∈ (s * t).divisors, if E.Coprime (s * t) then F s t (e * f) else 0
      else 0 := by
    have hst : 0 < s * t := Nat.mul_pos
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
      (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1
    by_cases hc : s.Coprime t
    · simp only [ite_eq_left hc]
      by_cases he : E.Coprime (s * t)
      · simp only [ite_eq_left he]
        exact quadratic_coprime_divisor_sum hE hst he (F s t)
      · simp only [ite_eq_right he, Finset.sum_const_zero]
    · simp only [ite_eq_right hc, Finset.sum_const_zero]
  calc
    _ = ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        ∑ e ∈ E.divisors, if s.Coprime t then
          ∑ f ∈ (s * t).divisors, if E.Coprime (s * t) then F s t (e * f) else 0
        else 0 := by
      exact Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun t ht => hlocal s hs t ht))
    _ = ∑ e ∈ E.divisors,
        ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
          if s.Coprime t then
            ∑ f ∈ (s * t).divisors, if E.Coprime (s * t) then F s t (e * f) else 0
          else 0 := by
      conv_lhs =>
        arg 2
        ext s
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_congr rfl (fun e _ => quadratic_coprime_divisor_reindex N
      (fun s t f => if E.Coprime (s * t) then F s t (e * f) else 0))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallCorrectionReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-kernel conductor corrections use the actual shorter Jacobi matrices -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadraticGcdBlockCoeff_coprime {R D n : ℕ} (v : ℕ → ℂ)
    (hn : Odd n) (h : ¬ (2 * D).Coprime n) : quadraticGcdBlockCoeff R D v n = 0 := by
  have hD : ¬ D.Coprime n := by
    intro hd
    exact h ((Nat.coprime_two_left.mpr hn).mul_left hd)
  simp [quadraticGcdBlockCoeff, quadraticRangeCoeff, quadraticDivisibilityCoeff, hD]

theorem quadratic_extra_weighted_reindex (N E : ℕ) (hE : 0 < E)
    (v w : ℕ → ℂ) (m : ℤ) (H : ℕ → ℂ)
    (hv : ∀ n ∈ oddSquarefreeRange (2 * N), ¬ E.Coprime n → v n = 0)
    (hw : ∀ n ∈ oddSquarefreeRange (2 * N), ¬ E.Coprime n → w n = 0) :
    (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then
        (v s * conj (w t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)) *
          ∑ d ∈ (E * (s * t)).divisors, H d else 0) =
      ∑ e ∈ E.divisors, ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
        H (e * d) * quadraticDivisorBilinear (2 * N) (2 * N) d v w m := by
  let A (s t : ℕ) : ℂ := v s * conj (w t) * (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ)
  have hz (s : ℕ) (hs : s ∈ oddSquarefreeRange (2 * N))
      (t : ℕ) (ht : t ∈ oddSquarefreeRange (2 * N))
      (he : ¬ E.Coprime (s * t)) : A s t = 0 := by
    by_cases hes : E.Coprime s
    · have het : ¬ E.Coprime t := fun hh => he (hes.mul_right hh)
      simp [A, hw t ht het]
    · simp [A, hv s hs hes]
  have heq : (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then A s t * ∑ d ∈ (E * (s * t)).divisors, H d else 0) =
      ∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
        if s.Coprime t then
          if E.Coprime (s * t) then ∑ d ∈ (E * (s * t)).divisors, A s t * H d else 0
        else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hc : s.Coprime t
    · rw [ite_eq_left hc, ite_eq_left hc]
      by_cases he : E.Coprime (s * t)
      · rw [ite_eq_left he, Finset.mul_sum]
      · rw [ite_eq_right he, hz s hs t ht he, zero_mul]
    · rw [ite_eq_right hc, ite_eq_right hc]
  change (∑ s ∈ oddSquarefreeRange (2 * N), ∑ t ∈ oddSquarefreeRange (2 * N),
      if s.Coprime t then A s t * ∑ d ∈ (E * (s * t)).divisors, H d else 0) = _
  rw [heq, quadratic_extra_divisor_reindex N E hE (fun s t d => A s t * H d)]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro d _
  unfold quadraticDivisorBilinear
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : s.Coprime t ∧ d ∣ s * t
  · rw [ite_eq_left hc, ite_eq_left hc]
    by_cases he : E.Coprime (s * t)
    · rw [ite_eq_left he]
      dsimp [A]
      ring
    · rw [ite_eq_right he]
      have hh := hz s hs t ht he
      dsimp [A] at hh
      rw [one_mul]
      rw [mul_assoc, mul_assoc] at hh
      calc
        0 = H (e * d) * 0 := by ring
        _ = _ := by rw [← hh]; ring
  · rw [ite_eq_right hc, ite_eq_right hc]
    simp

theorem quadratic_gcd_small_correction_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (m : ℤ) (H : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) *
        ((jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (2 * D * quadraticPairKernel z.1 z.2).divisors, H d)) =
      ∑ e ∈ (2 * D).divisors, ∑ d ∈ Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2),
        H (e * d) * quadraticDivisorBilinear (2 * quadraticGcdBlockSize R D)
          (2 * quadraticGcdBlockSize R D) d
            (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w) m := by
  have hDpos := Nat.pos_of_ne_zero hD.ne_zero
  rw [quadratic_gcd_block_reindex hD ho v w
    (fun q => (jacobiSym m q : ℂ) * ∑ d ∈ (2 * D * q).divisors, H d)]
  rw [quadratic_coprime_kernel_sum (2 * quadraticGcdBlockSize R D)
    (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w)
    (fun q => (jacobiSym m q : ℂ) * ∑ d ∈ (2 * D * q).divisors, H d)]
  rw [← quadratic_extra_weighted_reindex _ (2 * D) (by positivity : 0 < 2 * D)
    (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w) m H
    (fun n hn h => quadraticGcdBlockCoeff_coprime v (Finset.mem_filter.mp hn).2.1 h)
    (fun n hn h => quadraticGcdBlockCoeff_coprime w (Finset.mem_filter.mp hn).2.1 h)]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : s.Coprime t
  · rw [ite_eq_left hc, ite_eq_left hc,
      jacobiSym.mul_right' m (Finset.mem_filter.mp hs).2.2.ne_zero
        (Finset.mem_filter.mp ht).2.2.ne_zero, Int.cast_mul]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallFilteredReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the literal small-kernel divisor cutoffs after gcd removal -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_small_filtered_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (m : ℤ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (w z.2) *
      ((jacobiSym m (quadraticPairKernel z.1 z.2) : ℂ) *
        ∑ d ∈ (2 * D * quadraticPairKernel z.1 z.2).divisors.filter P, f d)) =
      ∑ e ∈ (2 * D).divisors, ∑ d ∈ Finset.Icc 1 ((2 * quadraticGcdBlockSize R D) ^ 2),
        if P (e * d) then f (e * d) * quadraticDivisorBilinear
          (2 * quadraticGcdBlockSize R D) (2 * quadraticGcdBlockSize R D) d
            (quadraticGcdBlockCoeff R D v) (quadraticGcdBlockCoeff R D w) m else 0 := by
  simpa only [Finset.sum_filter, ite_mul, zero_mul] using
    quadratic_gcd_small_correction_reindex hD ho v w m (fun d => if P d then f d else 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallCorrectionIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal small-kernel correction is the two bounded full sums -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

theorem quadratic_gcd_small_frequency_split {M : ℝ} (hM : 0 < M) (J : ℝ)
    {R D b : ℕ} (hD : Squarefree D) (ho : Odd D) (v w : ℕ → ℂ) :
    let N := quadraticGcdBlockSize R D
    let v' := quadraticGcdBlockCoeff R D v
    let w' := quadraticGcdBlockCoeff R D w
    (∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (w z.2) *
      ((jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
        quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b)) =
    ∑ e ∈ (2 * D).divisors,
      (-(∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) * (Real.sqrt M : ℂ) *
        ((1 / (Real.sqrt b : ℂ)) *
          ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
            if quadraticSecondUpper (quadraticSmallScale M b) J < (e * d : ℕ) then
              ((ArithmeticFunction.moebius (e * d) : ℂ) / (e * d : ℕ)) *
                quadraticDivisorBilinear (2 * N) (2 * N) d v' w' b else 0) +
      ((Real.sqrt M : ℂ) / 2) * ((1 / (Real.sqrt b : ℂ)) *
        ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
          if quadraticSecondLower (quadraticSmallScale M b) J < (e * d : ℕ) ∧
              (e * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J then
            (((ArithmeticFunction.moebius (e * d) : ℂ) / (e * d : ℕ)) *
              quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest quadraticSieveWeight))
                (quadraticSmallScale M b / (e * d : ℕ)) (quadraticSecondWindow J)) *
              quadraticDivisorBilinear (2 * N) (2 * N) d v' w' b else 0)) := by
  classical
  dsimp only
  let X := quadraticSmallScale M b
  let U := quadraticSecondLower X J
  let V := quadraticSecondUpper X J
  let I := ∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)
  let f := fun d : ℕ => (ArithmeticFunction.moebius d : ℂ) / d
  let g := fun d : ℕ => f d *
    quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest quadraticSieveWeight))
      (X / d) (quadraticSecondWindow J)
  have he (q : ℕ) : 2 * (q * D) = 2 * D * q := by ring
  have hsplit : (∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (w z.2) *
      ((jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
        quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b)) =
      (-(X : ℂ) * I) * (∑ z ∈ quadraticGcdPairs (2 * R) D,
        v z.1 * conj (w z.2) * ((jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (2 * D * quadraticPairKernel z.1 z.2).divisors.filter (fun d : ℕ => V < d), f d)) +
      ((X : ℂ) / 2) * (∑ z ∈ quadraticGcdPairs (2 * R) D,
        v z.1 * conj (w z.2) * ((jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑ d ∈ (2 * D * quadraticPairKernel z.1 z.2).divisors.filter
            (fun d : ℕ => U < d ∧ (d : ℝ) ≤ V), g d)) := by
    conv_rhs => lhs; rw [Finset.mul_sum]
    conv_rhs => rhs; rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    simp only [quadraticSmallPairCorrection, he]
    change _ = (-(X : ℂ) * I) * _ + ((X : ℂ) / 2) * _
    dsimp only [f, g, X, U, V, I]
    ring
  have hlo := quadratic_gcd_small_filtered_reindex (R := R) hD ho v w b
    (fun d => V < (d : ℝ)) f
  have hmi := quadratic_gcd_small_filtered_reindex (R := R) hD ho v w b
    (fun d => U < (d : ℝ) ∧ (d : ℝ) ≤ V) g
  simp only [Finset.sum_filter] at hlo hmi
  rw [hsplit]
  simp only [Finset.sum_filter]
  conv_lhs => lhs; arg 2; rw [hlo]
  conv_lhs => rhs; arg 2; rw [hmi]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hX : (X : ℂ) = (Real.sqrt M : ℂ) / (Real.sqrt b : ℂ) := by
    dsimp [X, quadraticSmallScale]
    rw [Real.sqrt_div hM.le, Complex.ofReal_div]
  rw [hX]
  dsimp only [f, g, U, V, X, I]
  ring_nf

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallTotalIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full frequency assembly of the original small-kernel term -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

private theorem if_sum_zero (p : Prop) [Decidable p] (S : Finset ℕ) (f : ℕ → ℂ) :
    (if p then ∑ d ∈ S, f d else 0) = ∑ d ∈ S, if p then f d else 0 := by
  by_cases hp : p <;> simp [hp]

theorem quadratic_gcd_small_total_split {M : ℝ} (hM : 0 < M) (J : ℝ)
    {R D : ℕ} (hD : Squarefree D) (ho : Odd D) (K : ℕ) (v w : ℕ → ℂ) :
    let N := quadraticGcdBlockSize R D
    let v' := quadraticGcdBlockCoeff R D v
    let w' := quadraticGcdBlockCoeff R D w
    quadraticGcdSmallTotal M J R D K v w =
      ∑ e ∈ (2 * D).divisors,
        (-(∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) * (Real.sqrt M : ℂ) *
          quadraticFullSmallHighCorrection M J e N ((2 * N) ^ 2) K
            (fun _ b => D.Coprime b) v' w' +
        ((Real.sqrt M : ℂ) / 2) *
          quadraticFullSmallMiddleCorrection quadraticSieveWeight M J e N ((2 * N) ^ 2) K
            (quadraticSecondWindow J) (fun _ b => D.Coprime b) v' w') := by
  classical
  dsimp only
  let N := quadraticGcdBlockSize R D
  let v' := quadraticGcdBlockCoeff R D v
  let w' := quadraticGcdBlockCoeff R D w
  let hi := fun (e b : ℕ) => (1 / (Real.sqrt b : ℂ)) *
    ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
      if quadraticSecondUpper (quadraticSmallScale M b) J < (e * d : ℕ) then
        ((ArithmeticFunction.moebius (e * d) : ℂ) / (e * d : ℕ)) *
          quadraticDivisorBilinear (2 * N) (2 * N) d v' w' b else 0
  let mi := fun (e b : ℕ) => (1 / (Real.sqrt b : ℂ)) *
    ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
      if quadraticSecondLower (quadraticSmallScale M b) J < (e * d : ℕ) ∧
          (e * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J then
        (((ArithmeticFunction.moebius (e * d) : ℂ) / (e * d : ℕ)) *
          quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest quadraticSieveWeight))
            (quadraticSmallScale M b / (e * d : ℕ)) (quadraticSecondWindow J)) *
          quadraticDivisorBilinear (2 * N) (2 * N) d v' w' b else 0
  let cH := -(∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) * (Real.sqrt M : ℂ)
  let cM := (Real.sqrt M : ℂ) / 2
  have hh (e : ℕ) : (∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·), hi e b) =
      quadraticFullSmallHighCorrection M J e N ((2 * N) ^ 2) K (fun _ b => D.Coprime b) v' w' := by
    dsimp only [hi]
    simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    simp_rw [if_sum_zero]
    rw [Finset.sum_comm]
    unfold quadraticFullSmallHighCorrection
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only
    split_ifs <;> first | tauto | ring
  have hm (e : ℕ) : (∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·), mi e b) =
      quadraticFullSmallMiddleCorrection quadraticSieveWeight M J e N ((2 * N) ^ 2) K
        (quadraticSecondWindow J) (fun _ b => D.Coprime b) v' w' := by
    dsimp only [mi]
    simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    simp_rw [if_sum_zero]
    rw [Finset.sum_comm]
    unfold quadraticFullSmallMiddleCorrection
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only
    split_ifs <;> first | tauto | ring
  have hp (b : ℕ) (_hb : b ∈ (oddSquarefreeRange K).filter (D.Coprime ·)) :
      (∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (w z.2) *
        ((jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
          quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b)) =
        ∑ e ∈ (2 * D).divisors, (cH * hi e b + cM * mi e b) := by
    exact quadratic_gcd_small_frequency_split (R := R) (b := b) hM J hD ho v w
  unfold quadraticGcdSmallTotal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [show (∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
      ∑ z ∈ quadraticGcdPairs (2 * R) D, _) =
        ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
          ∑ e ∈ (2 * D).divisors, (cH * hi e b + cM * mi e b) from Finset.sum_congr rfl hp]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hh, hm]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallEnvelope
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common bound for the two literal small-kernel corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap

theorem quadraticSmallCorrectionScalar_nonneg {C ε ξ M J : ℝ}
    (hC : 0 ≤ C) (_hM : 0 ≤ M) (hJ : 0 ≤ J) (E N Q K L : ℕ) :
    0 ≤ quadraticSmallCorrectionScalar C ε ξ M J E N Q K L := by
  unfold quadraticSmallCorrectionScalar
  positivity

theorem quadraticSmallCorrectionScalar_scale (C ε ξ M J : ℝ) (E N Q K L : ℕ) :
    quadraticSmallCorrectionScalar C ε ξ M J E N Q K L =
      C * quadraticSmallCorrectionScalar 1 ε ξ M J E N Q K L := by
  unfold quadraticSmallCorrectionScalar
  ring

theorem quadraticSmallCorrectionScalar_mono {C ε ξ M J : ℝ}
    (hC : 0 ≤ C) (hJ : 0 ≤ J) {E F N Q K L : ℕ} (hEF : E ≤ F) :
    quadraticSmallCorrectionScalar C ε ξ M J E N Q K L ≤
      quadraticSmallCorrectionScalar C ε ξ M J F N Q K L := by
  unfold quadraticSmallCorrectionScalar
  gcongr

theorem quadratic_small_combination_growth :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε ξ M J : ℝ,
      0 ≤ C → 0 ≤ ε → 1 / 2 ≤ ξ → ξ ≤ 2 → ∀ E N Q K L : ℕ,
      0 < M → 1 ≤ E → 0 < N → 1 ≤ Q → 0 < K → 1 ≤ J →
      ∀ R : ℕ → ℕ → Prop, ∀ v : ℕ → ℂ,
      (∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
        QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
          (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖(-(∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) * (Real.sqrt M : ℂ)) *
          quadraticFullSmallHighCorrection M J E N Q K R v v +
        ((Real.sqrt M : ℂ) / 2) * quadraticFullSmallMiddleCorrection quadraticSieveWeight M J E N Q K L R v v‖ ≤
        A * quadraticSmallCorrectionScalar C ε ξ M J E N Q K L * quadraticDivisorMoment (2 * N) v := by
  let I := ∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)
  let W := quadraticSmallFourierBound quadraticSieveWeight
  have hW : 0 ≤ W := quadraticSmallFourierBound_nonneg _
  let A := 1 + 64 * ‖I‖ + 64 * W
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro C ε ξ M J hC hε hξ hξ' E N Q K L hM hE hN hQ hK hJ R v hmat
  let S := quadraticSmallCorrectionScalar C ε ξ M J E N Q K L * quadraticDivisorMoment (2 * N) v
  have hv : 0 ≤ quadraticDivisorMoment (2 * N) v := by unfold quadraticDivisorMoment; positivity
  have hS : 0 ≤ S := mul_nonneg
    (quadraticSmallCorrectionScalar_nonneg hC hM.le (by linarith) _ _ _ _ _) hv
  have hh := quadratic_full_small_high_growth hC hε hξ hξ' hM hE hN hQ hK hJ R v v hmat
  have hm := quadratic_full_small_middle_growth quadraticSieveWeight
    hC hε hξ hξ' hM hE hN hQ hK hJ (L := L) R v v hmat
  rw [Real.mul_self_sqrt hv] at hh hm
  have hhigh : ‖(Real.sqrt M : ℂ) * quadraticFullSmallHighCorrection M J E N Q K R v v‖ ≤ 64 * S := by
    apply hh.trans
    let T := ((Nat.log 2 K + 1 : ℕ) : ℝ) * ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
      ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        (C * (4 * (K : ℝ) * N) ^ ε * (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + 8 * E * J * N)) *
          quadraticDivisorMoment (2 * N) v
    have hT : 0 ≤ T := by dsimp [T]; positivity
    calc
      _ = 64 * T := by dsimp [T]; ring
      _ ≤ 64 * ((2 * L + 1) * T) := by nlinarith [show 0 ≤ (L : ℝ) by positivity]
      _ = 64 * S := by dsimp [S, quadraticSmallCorrectionScalar, T]; ring
  have hmiddle : ‖(Real.sqrt M : ℂ) *
      quadraticFullSmallMiddleCorrection quadraticSieveWeight M J E N Q K L R v v‖ ≤ 64 * W * S := by
    apply hm.trans_eq
    dsimp [S, W, quadraticSmallCorrectionScalar]
    ring
  let l := (Real.sqrt M : ℂ) * quadraticFullSmallHighCorrection M J E N Q K R v v
  let m := (Real.sqrt M : ℂ) * quadraticFullSmallMiddleCorrection quadraticSieveWeight M J E N Q K L R v v
  have hid : (Real.sqrt M : ℂ) / 2 = (1 / 2 : ℂ) * (Real.sqrt M : ℂ) := by ring
  rw [hid]
  simp only [mul_assoc]
  change ‖(-I) * l + (1 / 2 : ℂ) * m‖ ≤ A * S
  apply (norm_add_le _ _).trans
  rw [norm_mul (-I) l, norm_mul (1 / 2 : ℂ) m, norm_neg]
  have hl := mul_le_mul_of_nonneg_left hhigh (norm_nonneg I)
  have hm' := mul_le_mul (show ‖(1 / 2 : ℂ)‖ ≤ 1 by norm_num) hmiddle (norm_nonneg _) zero_le_one
  change ‖I‖ * ‖l‖ ≤ ‖I‖ * (64 * S) at hl
  change ‖(1 / 2 : ℂ)‖ * ‖m‖ ≤ 1 * (64 * W * S) at hm'
  dsimp only [A]
  nlinarith only [hl, hm', hS]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallTotalGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original small-kernel corrections bounded by the original coefficient energy -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_small_total_growth {ξ ε δ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ M J : ℝ, 0 < M → 1 ≤ J →
      ∀ R D K : ℕ, 0 < R → Squarefree D → Odd D → 0 < K → ∀ v : ℕ → ℂ,
        ‖quadraticGcdSmallTotal M J R D K v v‖ ≤
          A * (2 * D : ℝ) * quadraticSmallCorrectionScalar 1 ε ξ M J (2 * D)
            (quadraticGcdBlockSize R D) ((2 * quadraticGcdBlockSize R D) ^ 2) K
              (quadraticSecondWindow J) * (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A₀, hA₀, hc⟩ := quadratic_small_combination_growth
  obtain ⟨C, hC, hmat⟩ := quadratic_growth_cutoff_bounds h hε
  obtain ⟨A₁, hA₁, hmom⟩ := quadratic_gcd_block_divisor_moment δ hδ
  refine ⟨A₀ * C * A₁, by positivity, ?_⟩
  intro M J hM hJ R D K hR hD ho hK v
  have hD₀ : 0 < D := Nat.pos_of_ne_zero hD.ne_zero
  let N := quadraticGcdBlockSize R D
  let v' := quadraticGcdBlockCoeff R D v
  have hN : 0 < N := quadraticGcdBlockSize_pos hR hD₀
  have hQ : 1 ≤ (2 * N) ^ 2 := by nlinarith
  let S := quadraticSmallCorrectionScalar C ε ξ M J (2 * D) N ((2 * N) ^ 2) K (quadraticSecondWindow J)
  have hS : 0 ≤ S := quadraticSmallCorrectionScalar_nonneg hC.le hM.le (by linarith) _ _ _ _ _
  let T := A₀ * S * (A₁ * (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v)
  have hv : 0 ≤ quadraticSieveEnergy (2 * R) v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (mul_nonneg hA₀.le hS)
      (mul_nonneg (mul_nonneg hA₁.le (Real.rpow_nonneg (by positivity) _)) hv)
  rw [quadratic_gcd_small_total_split hM J hD ho]
  calc
    _ ≤ ∑ e ∈ (2 * D).divisors, T := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      have he₀ := Nat.pos_of_mem_divisors he
      have heD := Nat.le_of_dvd (by omega : 0 < 2 * D) (Nat.dvd_of_mem_divisors he)
      have hb := hc C ε ξ M J hC.le hε.le hξ hξ' e N ((2 * N) ^ 2) K (quadraticSecondWindow J)
        hM he₀ hN hQ hK hJ (fun _ b => D.Coprime b) v'
        (fun B hB _ => hmat (2 * B) (2 * N) (by omega) (by omega))
      apply hb.trans
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ hA₀.le
        exact quadraticSmallCorrectionScalar_mono hC.le (by linarith) heD
      · exact hmom R D hD ho v
      · exact Finset.sum_nonneg (fun _ _ => by positivity)
      · exact mul_nonneg hA₀.le hS
    _ = ((2 * D).divisors.card : ℝ) * T := by simp
    _ ≤ (2 * D : ℝ) * T := by
      apply mul_le_mul_of_nonneg_right _ hT
      exact_mod_cast Nat.card_divisors_le_self (2 * D)
    _ = _ := by
      dsimp only [T, S, N]
      rw [quadraticSmallCorrectionScalar_scale]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdCorrectionsGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All original gcd corrections are bounded by the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_corrections_first_small (M R D K : ℕ) (J : ℝ) (v : ℕ → ℂ) :
    quadraticGcdMomentCorrections M R K D J v =
      (∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (v z.2) *
        quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J) -
      quadraticGcdSmallTotal M J R D K v v := by
  unfold quadraticGcdMomentCorrections quadraticGcdSmallTotal
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem quadratic_gcd_corrections_growth {ξ ε δ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D ≤ R → 0 < K →
      ∀ J : ℝ, 1 ≤ J → ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖quadraticGcdMomentCorrections M R K D J v‖ ≤
          A * (2 * D : ℝ) *
            (quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
                ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) +
              quadraticSmallCorrectionScalar 1 ε ξ M J (2 * D) (quadraticGcdBlockSize R D)
                ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J)) *
                  (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A₁, hA₁, hf⟩ := quadratic_first_total_growth h hξ hξ' hε hδ
  obtain ⟨A₂, hA₂, hs⟩ := quadratic_small_total_growth h hξ hξ' hε hδ
  refine ⟨A₁ + A₂, by positivity, ?_⟩
  intro M R D K hM hR hD ho hDR hK J hJ v hv
  have hfirst := hf M R D K hM hR hD ho hDR hK J hJ v hv
  have hsmall := hs M J (by exact_mod_cast hM) hJ R D K hR hD ho hK v
  let F := quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
    ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J)
  let S := quadraticSmallCorrectionScalar 1 ε ξ M J (2 * D) (quadraticGcdBlockSize R D)
    ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J)
  let P := (2 * D : ℝ) * (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v
  have hF : 0 ≤ F := quadraticCorrectionScalar_nonneg zero_le_one (by positivity) (by linarith) _ _ _ _
  have hS : 0 ≤ S := quadraticSmallCorrectionScalar_nonneg zero_le_one (by positivity) (by linarith) _ _ _ _ _
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [quadratic_gcd_corrections_first_small]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ A₁ * F * P + A₂ * S * P := by
      apply add_le_add
      · convert hfirst using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [F, P]; ring)
      · convert hsmall using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [S, P]; ring)
    _ ≤ (A₁ + A₂) * (F + S) * P := by
      nlinarith only [mul_nonneg (mul_nonneg hA₁.le hS) hP,
        mul_nonneg (mul_nonneg hA₂.le hF) hP]
    _ = _ := by dsimp [F, S, P]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionPolynomial
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial and logarithmic costs of the original correction parameters -/

namespace Ostmann

theorem quadraticCorrectionLogFactor_nonneg (ε : ℝ) (N Q K L : ℕ) :
    0 ≤ quadraticCorrectionLogFactor ε N Q K L := by
  unfold quadraticCorrectionLogFactor
  positivity

theorem quadratic_correction_scalar_sum {M J ε ξ : ℝ} (hM : 0 ≤ M) (hJ : 1 ≤ J)
    {R D N Q K L : ℕ} (hD : 1 ≤ D) (hNR : N ≤ R) :
    (2 * D : ℝ) * (quadraticCorrectionScalar 1 ε ξ M J N Q K L +
      quadraticSmallCorrectionScalar 1 ε ξ M J (2 * D) N Q K L) ≤
      34 * (D : ℝ) ^ 2 * J * quadraticCorrectionLogFactor ε N Q K L *
        (M + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) := by
  let x := Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)
  let d := (D : ℝ) * J
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hjd : J ≤ d := by
    dsimp [d]
    nlinarith [show (1 : ℝ) ≤ D by exact_mod_cast hD]
  have hnr : (N : ℝ) ≤ R := by exact_mod_cast hNR
  have h₁ := mul_le_mul_of_nonneg_right hjd hM
  have h₂ := mul_le_mul_of_nonneg_right (show J + 1 ≤ 2 * d by linarith) hx
  have h₃ := mul_le_mul_of_nonneg_left hnr (show 0 ≤ 16 * d by positivity)
  have hs : J * (M + x) + (x + 16 * d * N) ≤ 17 * d * (M + R + x) := by
    nlinarith only [h₁, h₂, h₃, mul_nonneg hd hM,
      mul_nonneg hd (Nat.cast_nonneg R), mul_nonneg hd hx]
  have hG := quadraticCorrectionLogFactor_nonneg ε N Q K L
  have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg (show (0 : ℝ) ≤ 2 * D by positivity) hG)
  refine (le_of_eq ?_).trans (hh.trans (le_of_eq ?_)) <;>
    dsimp [quadraticCorrectionScalar, quadraticSmallCorrectionScalar, quadraticCorrectionLogFactor, d, x] <;>
    push_cast <;> ring

theorem quadratic_second_window_upper {J : ℝ} (hJ : 1 ≤ J) :
    (quadraticSecondWindow J : ℝ) ≤ 17 * J ^ 2 ∧
      2 * (quadraticSecondWindow J : ℝ) + 1 ≤ 35 * J ^ 2 := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 16 * J ^ 2 by positivity)
  change (quadraticSecondWindow J : ℝ) < 16 * J ^ 2 + 1 at hc
  have hj : 1 ≤ J ^ 2 := by nlinarith
  constructor <;> nlinarith

theorem quadratic_correction_logfactor_bound {ε η J : ℝ} (hη : 0 < η) (hJ : 1 ≤ J)
    {N R K : ℕ} (hN : 0 < N) (hNR : N ≤ R) (hK : 0 < K) :
    quadraticCorrectionLogFactor ε N ((2 * N) ^ 2) K (quadraticSecondWindow J) ≤
      70 * (1 + (η * Real.log 2)⁻¹) ^ 4 * J ^ 2 *
        (K : ℝ) ^ η * ((2 * (R : ℝ)) ^ 2) ^ η * ((2 * (R : ℝ)) ^ η) ^ 2 *
          (4 * (K : ℝ) * N) ^ ε := by
  let A := 1 + (η * Real.log 2)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcountK := quadratic_dyadic_count_bound η hη K hK
  have hcountQ := quadratic_dyadic_count_bound η hη ((2 * N) ^ 2) (by nlinarith)
  have hcountN := quadratic_dyadic_count_bound η hη (2 * N) (by omega)
  have hNreal : (N : ℝ) ≤ R := by exact_mod_cast hNR
  have hpowN : (2 * (N : ℝ)) ^ η ≤ (2 * (R : ℝ)) ^ η :=
    Real.rpow_le_rpow (by positivity) (by linarith) hη.le
  have hpowQ : ((2 * (N : ℝ)) ^ 2) ^ η ≤ ((2 * (R : ℝ)) ^ 2) ^ η := by
    apply Real.rpow_le_rpow (by positivity) _ hη.le
    nlinarith [sq_nonneg ((R : ℝ) - N)]
  have hlogN : ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ≤ A * (2 * (R : ℝ)) ^ η := by
    apply hcountN.trans
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left hpowN hA
  have hlogQ : ((Nat.log 2 ((2 * N) ^ 2) + 2 : ℕ) : ℝ) ≤
      2 * A * ((2 * (R : ℝ)) ^ 2) ^ η := by
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hcountQ
    have hh := hcountQ.trans (mul_le_mul_of_nonneg_left hpowQ hA)
    have hbase : 1 ≤ ((Nat.log 2 ((2 * N) ^ 2) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    push_cast at hbase hh ⊢
    nlinarith
  have hwin := (quadratic_second_window_upper hJ).2
  unfold quadraticCorrectionLogFactor
  calc
    _ ≤ (35 * J ^ 2) * (A * (K : ℝ) ^ η) *
        (2 * A * ((2 * (R : ℝ)) ^ 2) ^ η) * (A * (2 * (R : ℝ)) ^ η) ^ 2 *
          (4 * (K : ℝ) * N) ^ ε := by gcongr
    _ = _ := by dsimp [A]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrectionPowerCost
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the actual correction parameter costs into a small power -/

namespace Ostmann

theorem quadratic_original_power_cost {η X R N K : ℝ} (hη : 0 ≤ η) (hX : 1 ≤ X)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (hK : 0 ≤ K) (hRX : R ≤ X) (hNR : N ≤ R) (hKX : K ≤ X ^ 3) :
    (X ^ η) ^ 3 * K ^ η * ((2 * R) ^ 2) ^ η * ((2 * R) ^ η) ^ 2 *
      (4 * K * N) ^ η * (2 * R) ^ η ≤ 4 ^ (9 * η) * X ^ (36 * η) := by
  let Y := 4 * X ^ 4
  have hX₀ : 0 ≤ X := by linarith
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hX₁₄ : X ≤ X ^ 4 := by simpa using pow_le_pow_right₀ hX (by norm_num : 1 ≤ (4 : ℕ))
  have hX₂₄ : X ^ 2 ≤ X ^ 4 := pow_le_pow_right₀ hX (by norm_num)
  have hX₃₄ : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX (by norm_num)
  have hXY : X ≤ Y := by dsimp [Y]; nlinarith [pow_nonneg hX₀ 4]
  have hKY : K ≤ Y := by dsimp [Y]; nlinarith [pow_nonneg hX₀ 4]
  have hRY : 2 * R ≤ Y := by dsimp [Y]; nlinarith [pow_nonneg hX₀ 4]
  have hR₂Y : (2 * R) ^ 2 ≤ Y := by
    have hs : R ^ 2 ≤ X ^ 2 := by gcongr
    dsimp [Y]
    nlinarith
  have hKNY : 4 * K * N ≤ Y := by
    calc
      _ ≤ 4 * X ^ 3 * X := by gcongr; exact hNR.trans hRX
      _ = Y := by dsimp [Y]; ring
  have hpX := Real.rpow_le_rpow hX₀ hXY hη
  have hpK := Real.rpow_le_rpow hK hKY hη
  have hpR := Real.rpow_le_rpow (by positivity : 0 ≤ 2 * R) hRY hη
  have hpR₂ := Real.rpow_le_rpow (sq_nonneg (2 * R)) hR₂Y hη
  have hpKN := Real.rpow_le_rpow (by positivity : 0 ≤ 4 * K * N) hKNY hη
  calc
    _ ≤ (Y ^ η) ^ 3 * Y ^ η * Y ^ η * (Y ^ η) ^ 2 * Y ^ η * Y ^ η := by gcongr
    _ = (Y ^ η) ^ 9 := by ring
    _ = Y ^ (η * 9) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY]
      norm_num
    _ = 4 ^ (9 * η) * X ^ (36 * η) := by
      dsimp [Y]
      rw [Real.mul_rpow (by norm_num) (pow_nonneg hX₀ 4)]
      congr 1
      · congr 1; ring
      · rw [← Real.rpow_natCast, ← Real.rpow_mul hX₀]
        congr 1
        ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdCorrectionPowerSaving
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small-power bound for the complete original gcd correction -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_gcd_corrections_power_bound_oai {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D ≤ R → 0 < K →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 → ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖quadraticGcdMomentCorrections M R K D (((M : ℝ) * R) ^ η) v‖ ≤
          C * (D : ℝ) ^ 2 * ((M : ℝ) * R) ^ (36 * η) *
            ((M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A, hA, hc⟩ := quadratic_gcd_corrections_growth h hξ hξ' hη hη
  let B := 1 + (η * Real.log 2)⁻¹
  have hB : 0 < B := by dsimp [B]; positivity
  let C := 2380 * A * B ^ 4 * 4 ^ (9 * η)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M R D K hM hR hD ho hDR hK hKX v hv
  let X := (M : ℝ) * R
  let J := X ^ η
  let N := quadraticGcdBlockSize R D
  let Q := (2 * N) ^ 2
  let L := quadraticSecondWindow J
  let V := (M : ℝ) + R + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)
  let E := quadraticSieveEnergy (2 * R) v
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR₁ : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hM₁ hR₁
  have hJ : 1 ≤ J := Real.one_le_rpow hX hη.le
  have hN : 0 < N := quadraticGcdBlockSize_pos hR (Nat.pos_of_ne_zero hD.ne_zero)
  have hNR : N ≤ R := quadraticGcdBlockSize_le (Nat.pos_of_ne_zero hD.ne_zero)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb := hc M R D K hM hR hD ho hDR hK J hJ v hv
  have hscalar := quadratic_correction_scalar_sum (ε := η) (ξ := ξ)
    (show (0 : ℝ) ≤ M by positivity) hJ (show 1 ≤ D from Nat.pos_of_ne_zero hD.ne_zero) hNR
    (Q := Q) (K := K) (L := L)
  have hlog := quadratic_correction_logfactor_bound (ε := η) hη hJ hN hNR hK
  have hRX : (R : ℝ) ≤ X := by dsimp [X]; nlinarith
  have hpow := quadratic_original_power_cost hη.le hX (Nat.cast_nonneg R)
    (Nat.cast_nonneg N) (Nat.cast_nonneg K) hRX (by exact_mod_cast hNR) hKX
  calc
    _ ≤ A * (2 * D : ℝ) *
        (quadraticCorrectionScalar 1 η ξ M J N Q K L +
          quadraticSmallCorrectionScalar 1 η ξ M J (2 * D) N Q K L) * (2 * (R : ℝ)) ^ η * E := hb
    _ = A * ((2 * D : ℝ) *
        (quadraticCorrectionScalar 1 η ξ M J N Q K L +
          quadraticSmallCorrectionScalar 1 η ξ M J (2 * D) N Q K L)) * (2 * (R : ℝ)) ^ η * E := by ring
    _ ≤ A * (34 * (D : ℝ) ^ 2 * J * quadraticCorrectionLogFactor η N Q K L * V) *
        (2 * (R : ℝ)) ^ η * E := by gcongr
    _ ≤ A * (34 * (D : ℝ) ^ 2 * J *
        (70 * B ^ 4 * J ^ 2 * (K : ℝ) ^ η * ((2 * (R : ℝ)) ^ 2) ^ η *
          ((2 * (R : ℝ)) ^ η) ^ 2 * (4 * (K : ℝ) * N) ^ η) * V) *
        (2 * (R : ℝ)) ^ η * E := by gcongr
    _ = (2380 * A * B ^ 4 * (D : ℝ) ^ 2) *
        (J ^ 3 * (K : ℝ) ^ η * ((2 * (R : ℝ)) ^ 2) ^ η * ((2 * (R : ℝ)) ^ η) ^ 2 *
          (4 * (K : ℝ) * N) ^ η * (2 * (R : ℝ)) ^ η) * V * E := by ring
    _ ≤ (2380 * A * B ^ 4 * (D : ℝ) ^ 2) * (4 ^ (9 * η) * X ^ (36 * η)) * V * E := by gcongr
    _ = _ := by dsimp [C, X, V, E]; ring

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.quadratic_gcd_corrections_power_bound_oai := @OAI.Ostmann.quadratic_gcd_corrections_power_bound_oai
