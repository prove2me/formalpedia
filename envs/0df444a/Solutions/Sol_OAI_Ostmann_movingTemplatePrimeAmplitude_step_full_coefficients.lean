-- Prove2me | solution 1 for OAI.Ostmann.movingTemplatePrimeAmplitude_step_full_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:35:47.356598+00:00
-- url     : https://prove2.me/submissions/a5ae7601-aa8d-4b8d-a705-b7a554c4ec33

import Mathlib
import Definitions.Def_OAIQ095D008

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic separation of diagonal and transferred terms -/

namespace Ostmann

/-- A nonzero transferred frequency rules out a shared prime between
the two inherited products. All such primes exceed the frequency. -/
theorem transferred_products_coprime (HL HR : ℕ) (v w s P : ℤ) (hs : s ≠ 0)
    (hrel : v * HR - w * HL = s * P)
    (hsmall : ∀ q, q.Prime → q ∣ HL → q ∣ HR → s.natAbs < q)
    (hunit : ∀ q, q.Prime → q ∣ HL → q ∣ HR → IsCoprime (q : ℤ) P) :
    HL.Coprime HR := by
  apply Nat.coprime_of_dvd
  intro q hq hqL hqR
  have hL : (q : ℤ) ∣ (HL : ℤ) := Int.natCast_dvd_natCast.mpr hqL
  have hR : (q : ℤ) ∣ (HR : ℤ) := Int.natCast_dvd_natCast.mpr hqR
  have hN : (q : ℤ) ∣ v * HR - w * HL :=
    dvd_sub (dvd_mul_of_dvd_right hR v) (dvd_mul_of_dvd_right hL w)
  rw [hrel] at hN
  have hqs : (q : ℤ) ∣ s := (hunit q hq hqL hqR).dvd_of_dvd_mul_right hN
  have hle := Int.natAbs_le_of_dvd_ne_zero hqs hs
  simp only [Int.natAbs_natCast] at hle
  exact (not_le_of_gt (hsmall q hq hqL hqR)) hle

theorem large_prime_factors_coprime_frequency (H : ℕ) (v : ℤ) (hv : v ≠ 0)
    (hlarge : ∀ q, q.Prime → q ∣ H → v.natAbs < q) : H.Coprime v.natAbs := by
  apply Nat.coprime_of_dvd
  intro q hq hqH hqv
  exact (not_le_of_gt (hlarge q hq hqH))
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hv) hqv)

/-- Regrouping a nonzero numerator by the new signed frequency is
one-to-one, exactly as in the transfer substitution. -/
theorem unique_transferred_frequency (N P : ℤ) (hN : N ≠ 0) (hP : P ≠ 0)
    (hdiv : P ∣ N) : ∃! s : ℤ, s ≠ 0 ∧ N = s * P := by
  obtain ⟨s, hs⟩ := hdiv
  refine ⟨s, ⟨?_, by simpa only [mul_comm] using hs⟩, ?_⟩
  · intro hz
    simp only [hz, mul_zero] at hs
    exact hN hs
  · intro t ht
    apply mul_right_cancel₀ hP
    rw [← ht.2, hs, mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferFrequencyRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite range of a transferred frequency -/

namespace Ostmann

open scoped BigOperators Classical

/-- The product ranges supply the frequency cutoff without rounding a
quotient or introducing an independent frequency assumption. -/
theorem transferred_frequency_bound (M L R B H V : ℕ) (s v w : ℤ)
    (hM : 0 < M) (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hL : L ≤ H) (hR : R ≤ H)
    (hscale : 2 * B * H ≤ V * M)
    (hrel : v * R - w * L = s * M) : s.natAbs ≤ V := by
  have he : s.natAbs * M = (v * R - w * L).natAbs := by
    rw [hrel, Int.natAbs_mul, Int.natAbs_natCast]
  have hnum : (v * R - w * L).natAbs ≤ 2 * B * H := by
    calc
      _ ≤ (v * R).natAbs + (w * L).natAbs := Int.natAbs_sub_le _ _
      _ = v.natAbs * R + w.natAbs * L := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ B * H + B * H := Nat.add_le_add (Nat.mul_le_mul hv hR) (Nat.mul_le_mul hw hL)
      _ = 2 * B * H := by ring
  exact Nat.le_of_mul_le_mul_right ((he.trans_le hnum).trans hscale) hM

/-- One integer quotient contributes once, including its sign. -/
theorem transferred_frequency_sum (M : ℕ) (hM : 0 < M) (N : ℤ)
    (S : Finset ℤ) (hS : ∀ s : ℤ, s ≠ 0 → N = s * M → s ∈ S) (z : ℂ) :
    (if N ≠ 0 ∧ (M : ℤ) ∣ N then z else 0) =
      ∑ s ∈ S, if s ≠ 0 ∧ N = s * M then z else 0 := by
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  by_cases h : N ≠ 0 ∧ (M : ℤ) ∣ N
  · obtain ⟨s, hs, huniq⟩ := unique_transferred_frequency N M h.1 hM0 h.2
    rw [ite_eq_left h, Finset.sum_eq_single s]
    · rw [ite_eq_left hs]
    · intro t _ hts
      rw [ite_eq_right]
      intro ht
      exact hts (huniq t ht)
    · exact fun hnot => (hnot (hS s hs.1 hs.2)).elim
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro s _
    rw [ite_eq_right]
    rintro ⟨hs, he⟩
    apply h
    refine ⟨?_, ?_⟩
    · rw [he]
      exact mul_ne_zero hs hM0
    · rw [he]
      exact dvd_mul_left (M : ℤ) s

/-- A prime-product range is enough to cover every off-diagonal term by
its actual new root frequency. -/
theorem transferred_frequency_sum_bounded (M L R B H V : ℕ)
    (hM : 0 < M) (v w : ℤ) (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hL : L ≤ H) (hR : R ≤ H) (hscale : 2 * B * H ≤ V * M) (z : ℂ) :
    (if v * R - w * L ≠ 0 ∧ (M : ℤ) ∣ v * R - w * L then z else 0) =
      ∑ s ∈ transferFrequencyRange V,
        if s ≠ 0 ∧ v * R - w * L = s * M then z else 0 := by
  apply transferred_frequency_sum M hM
  intro s _ hs
  exact (mem_transferFrequencyRange V s).mpr
    (transferred_frequency_bound M L R B H V s v w hM hv hw hL hR hscale hs)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TransferCauchy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Cauchy--Schwarz step in the history transfer -/

namespace Ostmann

open scoped BigOperators

theorem complex_pairing_sq_le {A : Type*} [Fintype A] (F G : A → ℂ) :
    ‖∑ a, F a * G a‖ ^ 2 ≤ (∑ a, ‖F a‖ ^ 2) * ∑ a, ‖G a‖ ^ 2 := by
  have hnorm : ‖∑ a, F a * G a‖ ≤ ∑ a, ‖F a‖ * ‖G a‖ := by
    simpa only [norm_mul] using norm_sum_le (Finset.univ : Finset A) (fun a => F a * G a)
  have hnonneg : 0 ≤ ∑ a, ‖F a‖ * ‖G a‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun a => ‖F a‖) (fun a => ‖G a‖)
  nlinarith [norm_nonneg (∑ a, F a * G a)]

theorem probability_weighted_norm_sq_le {A : Type*} [Fintype A]
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hmass : ∑ a, μ a = 1) (F : A → ℂ) :
    ‖∑ a, (μ a : ℂ) * F a‖ ^ 2 ≤ ∑ a, μ a * ‖F a‖ ^ 2 := by
  have hnorm : ‖∑ a, (μ a : ℂ) * F a‖ ≤ ∑ a, μ a * ‖F a‖ := by
    calc
      _ ≤ ∑ a, ‖(μ a : ℂ) * F a‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ _)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun a => Real.sqrt (μ a)) (fun a => Real.sqrt (μ a) * ‖F a‖)
  have hsq (a : A) : Real.sqrt (μ a) ^ 2 = μ a := Real.sq_sqrt (hμ a)
  simp only [mul_pow, hsq] at hCS
  have hprod (a : A) : Real.sqrt (μ a) * (Real.sqrt (μ a) * ‖F a‖) = μ a * ‖F a‖ := by
    rw [← mul_assoc, ← pow_two, hsq]
  simp only [hprod, hmass, one_mul] at hCS
  have hnonneg : 0 ≤ ∑ a, μ a * ‖F a‖ :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hμ a) (norm_nonneg _)
  nlinarith [norm_nonneg (∑ a, (μ a : ℂ) * F a)]

/-- Each row can have its own modulus and hence its own finite index
type. The outer laws remain the original probability measures. -/
theorem finite_transfer_row_bound {A : Type*} [Fintype A] {T : A → Type*}
    [∀ a, Fintype (T a)] (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hmass : ∑ a, μ a = 1)
    (row coefficient : ∀ a, T a → ℂ) (M : A → ℝ)
    (hrow : ∀ a, (∑ t, ‖row a t‖ ^ 2) ≤ M a) :
    ‖∑ a, (μ a : ℂ) * ∑ t, row a t * coefficient a t‖ ^ 2 ≤
      ∑ a, μ a * (M a * ∑ t, ‖coefficient a t‖ ^ 2) := by
  apply (probability_weighted_norm_sq_le μ hμ hmass _).trans
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hμ a)
  exact (complex_pairing_sq_le (row a) (coefficient a)).trans
    (mul_le_mul_of_nonneg_right (hrow a) (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Probability-normalized additive Fourier identities

These finite identities provide the normalization used in Section 6.
Fourier inversion is the library's discrete Fourier inversion theorem.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem stdAddChar_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  rw [← Complex.inv_eq_conj hn, AddChar.map_neg_eq_inv]

theorem additiveFourier_inversion {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    f x = ∑ a : ZMod p, additiveFourier f a * ZMod.stdAddChar (a * x) := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at hinv
  calc
    f x = (p : ℂ)⁻¹ * ∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a := by
      simpa only [smul_eq_mul] using hinv.symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [additiveFourier]
      ring

theorem additiveFourier_conjugate_coefficient {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    (∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x)) =
      (p : ℂ) * conj (additiveFourier f a) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [additiveFourier_apply]
  simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj, neg_neg]
  rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem additiveFourier_energy {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖f x‖ ^ 2) =
      (p : ℝ) * ∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2 := by
  have heq : (∑ x : ZMod p, f x * conj (f x)) =
      (p : ℂ) * ∑ a : ZMod p, additiveFourier f a * conj (additiveFourier f a) := by
    calc
      _ = ∑ x : ZMod p, ∑ a : ZMod p,
          additiveFourier f a * ZMod.stdAddChar (a * x) * conj (f x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_mul, ← additiveFourier_inversion]
      _ = ∑ a : ZMod p, additiveFourier f a *
          ∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_comm x a]
        ring
      _ = _ := by
        simp_rw [additiveFourier_conjugate_coefficient]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum] at heq
  exact_mod_cast heq

/-- Additive Parseval with the manuscript's probability convention. -/
theorem additiveFourier_parseval {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2) =
      (p : ℝ)⁻¹ * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  rw [additiveFourier_energy f]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized Fourier transform of the actual centered density -/

namespace Ostmann

open scoped BigOperators

theorem densityFourier_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [densityFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  rw [← Finset.mul_sum, additiveFourier_parseval, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotResidueEquation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality of pivot residue keys is the exact transfer equation -/

namespace Ostmann

theorem pivot_residue_eq_iff (M L R : ℕ) (hLM : L.Coprime M) (hRM : R.Coprime M)
    (v w : ℤ) :
    (v : ZMod M) * (L : ZMod M)⁻¹ = (w : ZMod M) * (R : ZMod M)⁻¹ ↔
      (M : ℤ) ∣ v * R - w * L := by
  have hL := (ZMod.isUnit_iff_coprime L M).mpr hLM
  have hR := (ZMod.isUnit_iff_coprime R M).mpr hRM
  have hprod := hL.mul hR
  have he : ((v : ZMod M) * (L : ZMod M)⁻¹ - (w : ZMod M) * (R : ZMod M)⁻¹) *
      ((L : ZMod M) * R) = ((v * R - w * L : ℤ) : ZMod M) := by
    push_cast
    calc
      _ = (v : ZMod M) * ((L : ZMod M)⁻¹ * L) * R -
          (w : ZMod M) * ((R : ZMod M)⁻¹ * R) * L := by ring
      _ = _ := by rw [ZMod.inv_mul_of_unit _ hL, ZMod.inv_mul_of_unit _ hR]; ring
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    rw [h, sub_self, zero_mul] at he
    exact he.symm
  · intro h
    rw [h] at he
    have hz := congrArg (fun a : ZMod M => a * ((L : ZMod M) * R)⁻¹) he
    rw [mul_assoc, ZMod.mul_inv_of_unit _ hprod, mul_one, zero_mul] at hz
    exact sub_eq_zero.mp hz

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DiagonalTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the transfer diagonal before expanding the square -/

namespace Ostmann

open scoped BigOperators Classical

/-- The key comprises the inherited product and its frequency. Ordered
arrangements with that key are summed inside the square. -/
theorem diagonal_grouped_identity {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (z : A → ℂ) (w : K → ℂ) :
    (∑ a : A, ∑ b : A, if key a = key b then w (key a) * z a * star (z b) else 0) =
      ∑ k : K, w k * groupedCoefficient key z k * star (groupedCoefficient key z k) := by
  rw [Finset.sum_comm]
  symm
  unfold groupedCoefficient
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, apply_ite, star_zero,
    ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : key b = key a <;> simp [h]

theorem diagonal_real_eq_sum_sq {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (z : A → ℂ) (w : K → ℝ) :
    (∑ a : A, ∑ b : A,
      if key a = key b then (w (key a) : ℂ) * z a * star (z b) else 0).re =
      ∑ k : K, w k * ‖groupedCoefficient key z k‖ ^ 2 := by
  rw [diagonal_grouped_identity key z (fun k => (w k : ℂ))]
  simp only [mul_assoc, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotResidueGrouping
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the actual pivot row before the integer extension -/

namespace Ostmann

open scoped BigOperators Classical

theorem pivot_residue_grouping {A U : Type*} [Fintype A] [Fintype U]
    (key : A → U) (row : U → ℂ) (c : A → ℂ) :
    (∑ a, row (key a) * c a) = ∑ u, row u * groupedCoefficient key c u := by
  symm
  unfold groupedCoefficient
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotSquareExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The grouped square has the actual transfer divisibility condition -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem pivotResidueKey_eq_iff (M : ℕ) [NeZero M] (L R : ℕ)
    (hL : L.Coprime M) (hR : R.Coprime M) (v w : ℤ) :
    pivotResidueKey M L v = pivotResidueKey M R w ↔ (M : ℤ) ∣ v * R - w * L := by
  unfold pivotResidueKey
  rw [(ZMod.finEquiv M).symm.injective.eq_iff, pivot_residue_eq_iff M L R hL hR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferredPivotSubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem reconstructedPivot_of_eq (N s : ℤ) (hs : s ≠ 0) (M : ℕ)
    (h : N = s * M) : reconstructedPivot N s = M := by
  rw [reconstructedPivot, Int.ediv_eq_of_eq_mul_right hs h, Int.toNat_natCast]

theorem validTransferredPivot_of_eq (T : Finset ℕ) (N s : ℤ) (hs : s ≠ 0)
    (M : ℕ) (hM : 0 < M) (hMT : M ∈ T) (h : N = s * M) :
    validTransferredPivot T N s := by
  refine ⟨hs, ?_, ?_, ?_⟩
  · rw [h]
    exact dvd_mul_right s M
  · rw [Int.ediv_eq_of_eq_mul_right hs h]
    exact_mod_cast hM
  · rw [reconstructedPivot_of_eq N s hs M h]
    exact hMT

theorem validTransferredPivot_equation (T : Finset ℕ) (N s : ℤ)
    (h : validTransferredPivot T N s) :
    N = s * reconstructedPivot N s := by
  rw [reconstructedPivot, Int.toNat_of_nonneg h.2.2.1.le]
  exact (Int.mul_ediv_cancel' h.2.1).symm

/-- The sum over positive integers has exactly one retained term. This
identity is valid for arbitrary coefficients, including all inherited weights. -/
theorem transferred_pivot_substitution (T : Finset ℕ)
    (hT : ∀ M ∈ T, 0 < M) (N s : ℤ) (f : ℕ → ℂ) :
    (∑ M ∈ T, if s ≠ 0 ∧ N = s * M then f M else 0) =
      if validTransferredPivot T N s then f (reconstructedPivot N s) else 0 := by
  by_cases h : validTransferredPivot T N s
  · rw [ite_eq_left h, Finset.sum_eq_single (reconstructedPivot N s)]
    · rw [ite_eq_left ⟨h.1, validTransferredPivot_equation T N s h⟩]
    · intro M _ hne
      rw [ite_eq_right]
      rintro ⟨hs, he⟩
      exact hne (reconstructedPivot_of_eq N s hs M he).symm
    · exact fun hn => (hn h.2.2.2).elim
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro M hMT
    rw [ite_eq_right]
    rintro ⟨hs, he⟩
    exact h (validTransferredPivot_of_eq T N s hs M (hT M hMT) hMT he)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RecursiveTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with its actual reconstructed integer pivots -/

namespace Ostmann

open scoped BigOperators Classical

theorem ValidTransferNode.historyPivot_eq {State : Type*} {sys : TransferHistorySystem State}
    {σ : State} {s v w : ℤ} {P : ℕ} (h : ValidTransferNode sys σ s v w P) :
    historyPivot sys σ s v w = P :=
  reconstructedPivot_of_eq _ _ h.root_ne_zero P h.relation

/-- No witness choices enter the recursive weight: the integer equation
forces the pivot at every valid node. -/
theorem recursiveTransferWeight_node {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    recursiveTransferWeight sys leaf cutoff (n + 1) σ t =
      (cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
        recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
        star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2) := by
  simp only [recursiveTransferWeight, hP.historyPivot_eq, hP, ite_true, if_true]

theorem recursiveTransferWeight_nonzero_valid {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n σ t ≠ 0) :
    ValidTransferHistory sys n σ t := by
  induction n generalizing σ with
  | zero => trivial
  | succ n ih =>
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys leaf cutoff n σ t P hP] at ht
      have hl : recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 ≠ 0 := by
        intro hz
        simp only [hz, mul_zero, zero_mul, ne_eq, not_true_eq_false] at ht
      have hr : recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2 ≠ 0 := by
        intro hz
        simp only [hz, star_zero, mul_zero, ne_eq, not_true_eq_false] at ht
      exact ⟨P, hP, ih _ _ hl, ih _ _ hr⟩
    · exact False.elim (ht (by simp only [recursiveTransferWeight, P, hP, ite_false, if_false]))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Symmetries of the mixed Fourier bound

Conjugation and multiplication of the field argument by a unit preserve
both the energy hypothesis and the mixed character/Fourier bound. These
are the orientation changes used by the bottom pairs.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_conj {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => conj (f x)) a = conj (additiveFourier f (-a)) := by
  simp only [additiveFourier_apply, map_mul, map_inv₀, map_natCast, map_sum,
    stdAddChar_conj, mul_neg, neg_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleValues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

theorem movingNaturalProduct_append {σ : Type*} (value : σ → ℕ) (x y : List σ) :
    MovingSlotReversal.naturalProduct value (x ++ y) =
      MovingSlotReversal.naturalProduct value x * MovingSlotReversal.naturalProduct value y := by
  simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]

theorem movingSlotValues_flatten {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x : TreeLeafTuple (List σ) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n x) =
      treeLeafProduct n (movingSlotValues value n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [flattenMovingSlots, MovingSlotReversal.naturalProduct, List.map_append,
      List.prod_append, movingSlotValues, treeLeafProduct]
    exact congrArg₂ (· * ·) (ih x.1) (ih x.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOccurrenceUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit coefficients for the actual sampled occurrence paths -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.Frequencies.root {σ : Type*} {P : ℤ → Prop} {n : ℕ}
    {T : MovingSlotData σ n} (h : T.Frequencies P) : P T.frequency := by
  cases T with
  | leaf => exact h
  | node => exact h.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original recursive weight on moving-giant states

A reconstructed pivot is the composite `u*p`; only its quotient `p` becomes
the new giant. The compensation primes remain in the regular child lists.
-/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.Follows.root {σ : Type*} {n : ℕ} {T : MovingSlotData σ n}
    {t : FrequencyTree ℤ n} (h : T.Follows t) : T.frequency = frequencyRoot n t := by
  cases T with
  | leaf => exact h
  | node => exact h.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original regular slot lists in every moving child -/

namespace Ostmann
open scoped Classical

theorem flattenMovingSlots_append_perm {σ : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List σ) n) :
    (flattenMovingSlots n (appendMovingSlotLeaves n x y)).Perm
      (flattenMovingSlots n x ++ flattenMovingSlots n y) := by
  apply List.perm_iff_count.mpr
  intro a
  induction n with
  | zero => simp [flattenMovingSlots, appendMovingSlotLeaves]
  | succ n ih =>
    have hx := ih x.1 y.1
    have hy := ih x.2 y.2
    simpa only [flattenMovingSlots, appendMovingSlotLeaves, List.count_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg₂ (· + ·) hx hy

theorem buildMovingSlotData_regular_perm {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).regularSlots.Perm
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) := by
  cases samples with
  | leaf => exact List.Perm.refl _
  | @node n samples left right =>
    apply List.perm_iff_count.mpr
    intro a
    simp only [buildMovingSlotData, MovingSlotData.regularSlots, flattenMovingSlots,
      List.count_append]
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferIntegerPhases
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing the actual integer transfer equation at each surviving prime -/

namespace Ostmann

/-- A left-slot prime divides the left product, so its local equation loses
that term. No primality is required for this algebraic reduction. -/
theorem transfer_equation_mod_left (p L R M : ℕ) (v w s : ℤ)
    (hpL : p ∣ L) (h : v * R - w * L = s * M) :
    (v : ZMod p) * (R : ZMod p) = (s : ZMod p) * (M : ZMod p) := by
  have hL : (L : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hpL
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have he := congrArg (fun z : ℤ => (z : ZMod p)) h
  push_cast at he
  simpa only [hL, mul_zero, sub_zero] using he

theorem transfer_equation_mod_right (p L R M : ℕ) (v w s : ℤ)
    (hpR : p ∣ R) (h : v * R - w * L = s * M) :
    -(w : ZMod p) * (L : ZMod p) = (s : ZMod p) * (M : ZMod p) := by
  have hR : (R : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hpR
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have he := congrArg (fun z : ℤ => (z : ZMod p)) h
  push_cast at he
  simpa only [hR, mul_zero, zero_sub, neg_mul] using he

/-- Natural coprimality supplies the nonzero denominators in the prime field. -/
theorem zmod_natCast_ne_zero_of_coprime {p : ℕ} [Fact p.Prime] (a : ℕ)
    (h : a.Coprime p) : (a : ZMod p) ≠ 0 :=
  isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime a p).mpr h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PermutedAdditiveCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center additive phases cancel under the actual matching -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem tupleCofactor_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (i : I) :
    tupleCofactor (fun i => p (e i)) i = tupleCofactor p (e i) := by
  apply mul_left_cancel₀ (hp (e i))
  calc
    _ = ∏ j, p (e j) := tupleCofactor_mul _ i
    _ = ∏ j, p j := e.prod_comp p
    _ = _ := (tupleCofactor_mul p (e i)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant unit tests on signed residue representatives -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.frequencies_isCoprime {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (x : ℤ) :
    T.Frequencies (fun s => IsCoprime x s) ↔ IsCoprime x T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    simp only [Frequencies, frequencyProduct, IsCoprime.mul_right_iff, ihL, ihR, and_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotFieldBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original labelled bulk slots produce the quartet leaf arrays -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingSlotValues_indexed {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (s : TreeLeafTuple (List σ) n) (j : TreeLeafIndex n) :
    treeLeafTupleEquiv ℕ n (movingSlotValues value n s) j =
      MovingSlotReversal.naturalProduct value (treeLeafTupleEquiv (List σ) n s j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases j with
    | inl j => exact ih s.1 j
    | inr j => exact ih s.2 j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSmallFrequencyUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-prime frequency tests follow from the actual range separation -/

namespace Ostmann

theorem MovingSlotData.Frequencies.mono {σ : Type*} {P Q : ℤ → Prop}
    {n : ℕ} {T : MovingSlotData σ n} (h : T.Frequencies P) (hPQ : ∀ s, P s → Q s) :
    T.Frequencies Q := by
  induction T with
  | leaf => exact hPQ _ h
  | node s CL CR U left right ihL ihR => exact ⟨hPQ s h.1, ihL h.2.1, ihR h.2.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original independent compensation samples

Section 7.4, equations (7.10)--(7.11), samples one compensation vector at
each node. That vector is shared by its two children; samples subsequently
made in the children are independent. These are the literal finite priors,
before any distinctness or equality-pattern restriction.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem sum_movingSample_node {A M : Type*} [Fintype A] [AddCommMonoid M]
    (n : ℕ) (f : MovingSampleSlots A (n + 1) → M) :
    (∑ a, f a) = ∑ u : TreeLeafTuple (Fin 4 → A) n,
      ∑ l : MovingSampleSlots A n, ∑ r : MovingSampleSlots A n, f (.node u l r) := by
  have h := (movingSampleNodeEquiv A n).sum_comp f
  simp only [finite_univ_canonical] at h ⊢
  rw [← h]
  have h₁ := Fintype.sum_prod_type (fun x : TreeLeafTuple (Fin 4 → A) n ×
      MovingSampleSlots A n × MovingSampleSlots A n => f ((movingSampleNodeEquiv A n) x))
  simp only [finite_univ_canonical] at h₁
  rw [h₁]
  apply Finset.sum_congr rfl
  intro u _
  have h₂ := Fintype.sum_prod_type (fun x : MovingSampleSlots A n × MovingSampleSlots A n =>
    f (.node u x.1 x.2))
  simp only [finite_univ_canonical] at h₂
  refine Eq.trans ?_ h₂
  apply Finset.sum_congr rfl
  intro x _
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed coordinates for the actual internal prime samples

The coordinates count each sample when it is made, not its later occurrences
in descendant lists. Their number is independent of the number of bulk slots.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingCompensationPrior_indexed {A : Type*} (μ : A → ℝ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    movingCompensationPrior μ n a =
      ∏ t : TreeLeafIndex n, ∏ j : Fin 4, μ (treeLeafTupleEquiv (Fin 4 → A) n a t j) := by
  induction n with
  | zero =>
      change (∏ j : Fin 4, μ (a j)) = ∏ _t : Unit, ∏ j : Fin 4, μ (a j)
      simp only [Fintype.prod_unique]
  | succ n ih =>
      change movingCompensationPrior μ n a.1 * movingCompensationPrior μ n a.2 =
        ∏ t : TreeLeafIndex n ⊕ TreeLeafIndex n,
          ∏ j : Fin 4, μ (treeLeafTupleEquiv (Fin 4 → A) (n + 1) a t j)
      rw [Fintype.prod_sum_type, ih, ih]
      rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact compensation factors in the original history weight

Every sampled prime occurs once in the factor `u` at the node where it is
sampled. Its subsequent appearances in descendants do not add factors of `u`.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingCompensationProduct_indexed {A : Type*} (value : A → ℕ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n (movingCompensationSlots n a)) =
      ∏ t : TreeLeafIndex n, ∏ j : Fin 4, value (treeLeafTupleEquiv (Fin 4 → A) n a t j) := by
  induction n with
  | zero =>
      simp only [flattenMovingSlots, movingCompensationSlots, MovingSlotReversal.naturalProduct,
        List.map_ofFn, List.prod_ofFn]
      change (∏ j : Fin 4, value (a j)) = ∏ _t : Unit, ∏ j : Fin 4, value (a j)
      simp only [Fintype.prod_unique]
  | succ n ih =>
      simp only [movingCompensationSlots, flattenMovingSlots, movingNaturalProduct_append, ih]
      change _ = ∏ t : TreeLeafIndex n ⊕ TreeLeafIndex n,
        ∏ j : Fin 4, value (treeLeafTupleEquiv (Fin 4 → A) (n + 1) a t j)
      rw [Fintype.prod_sum_type]
      rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedPivotTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pivot transfer with bounds imposed on the actual nonzero support -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The residue identity is needed only for pairs with nonzero coefficients.
Thus the original coprimality indicator stays inside the coefficient. -/
theorem pivot_square_split_on_support {A : Type*} [Fintype A]
    (M : ℕ) [NeZero M] (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hL : ∀ a, c a ≠ 0 → (L a).Coprime M) :
    (∑ u : Fin M, ‖groupedCoefficient (fun a => pivotResidueKey M (L a) (v a)) c u‖ ^ 2) =
      (pivotDiagonal L v c).re + (pivotOffDiagonal M L v c).re := by
  have hh := diagonal_real_eq_sum_sq (fun a => pivotResidueKey M (L a) (v a)) c (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at hh
  rw [← hh, ← Complex.add_re]
  congr 1
  unfold pivotDiagonal pivotOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : c a = 0
  · simp [ha]
  by_cases hb : c b = 0
  · simp [hb]
  simp only [pivotResidueKey_eq_iff M (L a) (L b) (hL a ha) (hL b hb)]
  by_cases hz : v a * L b - v b * L a = 0
  · simp [hz]
  · by_cases hd : (M : ℤ) ∣ v a * L b - v b * L a <;> simp [hz, hd]

theorem pivotOffDiagonal_frequency_on_support {A : Type*} [Fintype A]
    (M B H V : ℕ) (hM : 0 < M) (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hv : ∀ a, c a ≠ 0 → (v a).natAbs ≤ B)
    (hL : ∀ a, c a ≠ 0 → L a ≤ H) (hscale : 2 * B * H ≤ V * M) :
    pivotOffDiagonal M L v c = ∑ s ∈ transferFrequencyRange V,
      ∑ a, ∑ b, if s ≠ 0 ∧ v a * L b - v b * L a = s * M
        then c a * conj (c b) else 0 := by
  have he (a b : A) :
      (if v a * L b - v b * L a ≠ 0 ∧ (M : ℤ) ∣ v a * L b - v b * L a
        then c a * conj (c b) else 0) =
      ∑ s ∈ transferFrequencyRange V,
        if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c a * conj (c b) else 0 := by
    by_cases ha : c a = 0
    · simp [ha]
    by_cases hb : c b = 0
    · simp [hb]
    exact transferred_frequency_sum_bounded M (L a) (L b) B H V hM (v a) (v b)
      (hv a ha) (hv b hb) (hL a ha) (hL b hb) hscale _
  unfold pivotOffDiagonal
  simp_rw [he]
  calc
    _ = ∑ a, ∑ s ∈ transferFrequencyRange V, ∑ b,
        if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c a * conj (c b) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotKeyReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduction of the actual integer pivot key at each constituent prime -/

namespace Ostmann

open scoped BigOperators Classical

theorem pivotResidueKey_val (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ) :
    ((pivotResidueKey M L v).val : ZMod M) = (v : ZMod M) * (L : ZMod M)⁻¹ := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M =>
    change (((v : ZMod (M + 1)) * (L : ZMod (M + 1))⁻¹).val : ZMod (M + 1)) = _
    exact ZMod.natCast_zmod_val _

/-- Key multiplication is valid already modulo the complete composite pivot. -/
theorem pivotResidueKey_mul (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ)
    (hL : L.Coprime M) :
    ((pivotResidueKey M L v).val : ZMod M) * (L : ZMod M) = (v : ZMod M) := by
  rw [pivotResidueKey_val, mul_assoc,
    ZMod.inv_mul_of_unit _ ((ZMod.isUnit_iff_coprime L M).mpr hL), mul_one]

/-- The same key reduces correctly at every prime dividing the pivot. No
field structure on the composite pivot ring is used. -/
theorem pivotResidueKey_mul_at_divisor (M : ℕ) [NeZero M] (L : ℕ) (v : ℤ)
    {p : ℕ} (hp : p ∣ M) (hL : L.Coprime M) :
    ((pivotResidueKey M L v).val : ZMod p) * (L : ZMod p) = (v : ZMod p) := by
  have he := congrArg (ZMod.castHom hp (ZMod p)) (pivotResidueKey_mul M L v hL)
  simpa only [map_mul, map_natCast, map_intCast] using he

theorem positiveIntegerPivotKey_mul_at_divisor (M : ℕ) (hM : 0 < M)
    (L : ℕ) (v : ℤ) {p : ℕ} (hp : p ∣ M) (hL : L.Coprime M) :
    ((positiveIntegerPivotKey M hM L v).val : ZMod p) * (L : ZMod p) = (v : ZMod p) := by
  let : NeZero M := ⟨hM.ne'⟩
  exact pivotResidueKey_mul_at_divisor M L v hp hL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferOutputSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coprimality and frequency units after the actual substitution -/

namespace Ostmann

/-- In the integer extension, the inherited coprimality with the erased
pivot implies precisely the common-prime unit condition used above. -/
theorem common_prime_pivot_unit (M L R : ℕ) (hLM : L.Coprime M)
    (q : ℕ) (_hq : q.Prime) (hqL : q ∣ L) (_hqR : q ∣ R) :
    IsCoprime (q : ℤ) (M : ℤ) := by
  have hqM : q.Coprime M := hLM.coprime_dvd_left hqL
  exact Int.isCoprime_iff_gcd_eq_one.mpr (by
    simpa only [Int.gcd_natCast_natCast] using hqM)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferRoundedCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural cutoffs supplied by the transfer's exponential ranges -/

namespace Ostmann

open Filter
open scoped Topology

theorem natural_exp_cutoff_bounds (E : ℝ) (hE : Real.log 2 ≤ E) :
    0 < ⌊Real.exp E⌋₊ ∧ (⌊Real.exp E⌋₊ : ℝ) ≤ Real.exp E ∧
      Real.exp E ≤ 2 * (⌊Real.exp E⌋₊ : ℝ) := by
  have hexp : (2 : ℝ) ≤ Real.exp E := by
    calc
      _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp E := Real.exp_le_exp.mpr hE
  have hn : 1 ≤ ⌊Real.exp E⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hnR : (1 : ℝ) ≤ ⌊Real.exp E⌋₊ := by exact_mod_cast hn
  exact ⟨hn, Nat.floor_le (Real.exp_pos _).le, by linarith [Nat.lt_floor_add_one (Real.exp E)]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampledRecursion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expanding the sampled giant recursion into its literal histories

This is the recursion of Section 7.4 (7.10)--(7.11), rather than the
whole-atom recursion of Section 4. Each root sample is used by both children.
The child sample trees are independent under the original finite law.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem buildMovingSlotData_frequencyTree {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk a).frequencyTree = t := by
  induction a with
  | leaf => rfl
  | node a l r hl hr =>
      exact Prod.ext rfl (Prod.ext (hl _ _ _) (hr _ _ _))

/-- The actual termwise node identity, including failed integer and
divisibility tests. The new giant is the quotient of the composite pivot. -/
theorem movingSample_weight_node {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1))
    (a : TreeLeafTuple (Fin 4 → σ) n) (l r : MovingSampleSlots σ n) (XL XR : ℕ) :
    let u := movingCompensationSlots n a
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let p := historyPivot (movingSlotSystem value childBound pivotBound)
      (movingRootState n t CL CR (flattenMovingSlots n u) XL XR) t.1
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
          MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) (n + 1)
      ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩ t =
        movingSampleRootFactor value childBound pivotBound E n t CL CR (flattenMovingSlots n u) XL XR *
          recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
            ⟨n, buildMovingSlotData n t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 l, p, XL⟩ t.2.1 *
          star (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
            ⟨n, buildMovingSlotData n t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 r, p, XR⟩ t.2.2) := by
  dsimp only
  let u := movingCompensationSlots n a
  let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
  let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
  let x : MovingSlotState σ :=
    ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩
  let y := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
  let sys := movingSlotSystem value childBound pivotBound
  let P := historyPivot sys y t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
  have hp : historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) = P := rfl
  have hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P ↔
      ValidTransferNode sys y t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P := by
    constructor <;> intro h <;>
      exact ⟨h.root_ne_zero, h.root_unit, h.relation, h.pivot_pos, h.pivot_bound,
        h.left_bound, h.right_bound, h.range_gap, h.pivot_unit⟩
  have hc : movingSlotCutoff value childBound pivotBound (movingLocalExtra E) x t.1
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
      movingSlotCutoff value childBound pivotBound E y t.1
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) := by
    unfold movingSlotCutoff
    have he : movingLocalExtra E x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
        E y t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) := by
      simp only [movingLocalExtra, x, buildMovingSlotData, MovingSlotData.rootData,
        buildMovingSlotData_frequencyTree]
      rfl
    rw [he]
    rfl
  change recursiveTransferWeight sys F _ (n + 1) x t = _
  rw [recursiveTransferWeight]
  simp only [hp]
  rw [hv, hc]
  by_cases h : ValidTransferNode sys y t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
  · simp only [h, ite_true, if_true]
    change _ = (if ValidTransferNode sys y t.1 _ _ P then _ else 0) * _ * _
    rw [ite_eq_left h]
    rfl
  · simp only [h, ite_false, if_false]
    change 0 = (if ValidTransferNode sys y t.1 _ _ P then _ else 0) * _ * _
    rw [ite_eq_right h, zero_mul, zero_mul]

theorem movingSampledWeight_node {σ : Type*} [Fintype σ] (value : σ → ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound F E (n + 1) t small bulk XL XR =
      ∑ a : TreeLeafTuple (Fin 4 → σ) n,
        let u := movingCompensationSlots n a
        let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
        let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
        let p := historyPivot (movingSlotSystem value childBound pivotBound)
          (movingRootState n t CL CR (flattenMovingSlots n u) XL XR) t.1
            (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
              MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
        (movingCompensationPrior (μ n) n a : ℂ) *
          movingSampleRootFactor value childBound pivotBound E n t CL CR (flattenMovingSlots n u) XL XR *
          movingSampledWeight value μ childBound pivotBound F E n t.2.1
            (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
          star (movingSampledWeight value μ childBound pivotBound F E n t.2.2
            (appendMovingSlotLeaves n u small.2) bulk.2 p XR) := by
  unfold movingSampledWeight
  rw [sum_movingSample_node]
  simp_rw [movingSample_weight_node]
  simp only [movingSamplesPrior, Complex.ofReal_mul, star_sum, star_mul,
    Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full original support as local guards in the sampled recursion

All current-state coprimalities and all descendant-frequency unit tests are
retained. This puts the existing fully supported coefficient into the local
recursion form, without conditioning any internal sample prior.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFullSupport_node {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (s : ℤ) (CL CR u : List σ) (l r : MovingSlotData σ n) (XL XR : ℕ) :
    let T := MovingSlotData.node s CL CR u l r
    let p := (MovingSlotData.step s CL CR u l r false).naturalPivot value XL XR
    movingFullSupport value outside T XL XR ↔
      movingLocalSupport value outside ⟨n + 1, T, XL, XR⟩ ∧
      movingFullSupport value outside l p XL ∧ movingFullSupport value outside r p XR := by
  simp only [movingFullSupport, movingLocalSupport, movingFullOutsidePairwise, movingNaturalGiantUnits]
  tauto

theorem movingSlotCutoff_guarded {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E) x s v w =
      if movingLocalSupport value outside x then
        movingSlotCutoff value childBound pivotBound E x s v w else 0 := by
  unfold movingSlotCutoff movingGuardedExtra
  split_ifs <;> rfl

/-- The fully supported original history coefficient equals the recursive
coefficient with the literal local support test at each node and leaf. -/
theorem movingSupportedWeight_recursive {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingGuardedLeaf value outside F)
      (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E))
      n ⟨n, T, XL, XR⟩ t =
        movingSupportedWeight value outside T XL XR
          (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound E) n ⟨n, T, XL, XR⟩ t) := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound E
  let cutg := movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E)
  induction T generalizing XL XR with
  | leaf s regular => rfl
  | @node n s CL CR u l r hl hr =>
      let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u l r, XL, XR⟩
      let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      let p := (MovingSlotData.step s CL CR u l r false).naturalPivot value XL XR
      have hp : P / MovingSlotReversal.naturalProduct value u = p := by
        simp only [P, p, historyPivot, sys, movingSlotSystem, x, MovingSlotState.leftProduct,
          MovingSlotState.rightProduct, MovingSlotReversal.naturalPivot, MovingSlotData.step,
          movingGiantPivot, Nat.mul_one, ← hT.1, ← hT.2.1.root, ← hT.2.2.root]
      by_cases hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
      · rw [recursiveTransferWeight_node sys _ cutg n x t P hv]
        change (cutg x t.1 _ _ : ℂ) *
            recursiveTransferWeight sys _ cutg n ⟨n, l, P / MovingSlotReversal.naturalProduct value u, XL⟩ t.2.1 *
            star (recursiveTransferWeight sys _ cutg n ⟨n, r, P / MovingSlotReversal.naturalProduct value u, XR⟩ t.2.2) = _
        rw [hp, hl t.2.1 hT.2.1 p XL, hr t.2.2 hT.2.2 p XR]
        have hg := movingSlotCutoff_guarded value outside childBound pivotBound E x
          t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
        change cutg x t.1 _ _ = if movingLocalSupport value outside x then cut x t.1 _ _ else 0 at hg
        rw [hg]
        unfold movingSupportedWeight
        have hs := movingFullSupport_node value outside s CL CR u l r XL XR
        dsimp only at hs
        rw [hs]
        rw [recursiveTransferWeight_node sys F cut n x t P hv]
        have hleft : sys.leftState x P =
            ⟨n, l, P / MovingSlotReversal.naturalProduct value u, XL⟩ := rfl
        have hright : sys.rightState x P =
            ⟨n, r, P / MovingSlotReversal.naturalProduct value u, XR⟩ := rfl
        rw [hleft, hright, hp]
        by_cases hA : movingLocalSupport value outside x <;>
          by_cases hB : movingFullSupport value outside l p XL <;>
          by_cases hC : movingFullSupport value outside r p XR
        all_goals dsimp only [x, p] at hA hB hC ⊢
        all_goals simp only [hA, hB, hC, and_true, and_false,
          ite_true, if_true, ite_false, if_false, Complex.ofReal_zero, zero_mul, mul_zero, star_zero]
        rfl
      · have hz₁ : recursiveTransferWeight sys (movingGuardedLeaf value outside F) cutg
            (n + 1) x t = 0 := by simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
        have hz₂ : recursiveTransferWeight sys F cut (n + 1) x t = 0 := by
          simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
        rw [hz₁, hz₂]
        unfold movingSupportedWeight
        split_ifs <;> rfl

theorem movingFrequencySkeleton_frequencyTree (σ : Type*) (n : ℕ)
    (t : FrequencyTree ℤ n) :
    (movingFrequencySkeleton σ n t).frequencyTree = t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [movingFrequencySkeleton, MovingSlotData.frequencyTree, ih]
    rfl

theorem MovingSlotData.skeleton_frequencyProduct {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) :
    (movingFrequencySkeleton σ n T.frequencyTree).frequencyProduct = T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR u l r hl hr =>
    simp only [MovingSlotData.frequencyTree, movingFrequencySkeleton, frequencyProduct, hl, hr]

theorem MovingSlotData.rootData_regularSlots {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.regularSlots = T.regularSlots := by
  cases T <;> rfl

theorem MovingSlotData.rootData_frequencyProduct {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.frequencyProduct = T.frequencyProduct := by
  cases T with
  | leaf => rfl
  | node s CL CR u l r =>
    simp only [rootData, frequencyProduct, skeleton_frequencyProduct]

theorem MovingSlotData.rootData_idempotent {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.rootData = T.rootData := by
  cases T with
  | leaf => rfl
  | node s CL CR u l r =>
    simp only [rootData, movingFrequencySkeleton_frequencyTree]

theorem movingLocalSupport_rootData {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (x : MovingSlotState σ) :
    movingLocalSupport value outside ⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ ↔
      movingLocalSupport value outside x := by
  simp only [movingLocalSupport, MovingSlotData.currentSlots, movingLocalGiantUnits,
    MovingSlotData.rootData_regularSlots, MovingSlotData.rootData_frequencyProduct]

theorem movingLocalExtra_guarded {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    movingLocalExtra (movingGuardedExtra value outside (movingLocalExtra E)) =
      movingGuardedExtra value outside (movingLocalExtra E) := by
  funext x s v w
  simp only [movingLocalExtra, movingGuardedExtra, movingLocalSupport_rootData,
    MovingSlotData.rootData_idempotent]

/-- The sample expansion of the fully supported original coefficient. Every
sample retains its original weight, including samples whose support fails. -/
theorem movingSampledWeight_supported {σ : Type*} [Fintype σ] (value : σ → ℕ)
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
      (movingGuardedExtra value outside (movingLocalExtra E)) n t small bulk XL XR =
      ∑ a : MovingSampleSlots σ n, (movingSamplesPrior μ a : ℂ) *
        movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
          (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
            ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t) := by
  unfold movingSampledWeight
  rw [movingLocalExtra_guarded]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingSupportedWeight_recursive value outside childBound pivotBound F (movingLocalExtra E)
    _ t (buildMovingSlotData_follows n t small bulk a)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveCompensation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting compensation from the actual supported recursion -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSlotCutoff_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E) x s v w =
      (x.compensation value : ℝ) * movingSlotCutoff value childBound pivotBound E x s v w := by
  unfold movingSlotCutoff movingCompensatedExtra
  split_ifs <;> simp only [mul_zero]

theorem MovingSlotState.compensation_rootData {σ : Type*} (value : σ → ℕ)
    (x : MovingSlotState σ) :
    (⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ : MovingSlotState σ).compensation value =
      x.compensation value := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> rfl

theorem movingLocalExtra_compensated {σ : Type*} (value : σ → ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    movingLocalExtra (movingCompensatedExtra value E) =
      movingCompensatedExtra value (movingLocalExtra E) := by
  funext x s v w
  simp only [movingLocalExtra, movingCompensatedExtra, MovingSlotState.compensation_rootData]

/-- Each node contributes its newly sampled compensation exactly once,
including off-support samples where both sides vanish. -/
theorem movingRecursiveWeight_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E)) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t =
        (movingSampleProduct value a : ℂ) *
          recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound E) n
            ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound E
  let cutc := movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E)
  induction a generalizing XL XR with
  | leaf => simp only [movingSampleProduct, Nat.cast_one, one_mul, recursiveTransferWeight]
  | @node n a l r hl hr =>
    let x : MovingSlotState σ :=
      ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩
    let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys F cutc n x t P hv,
        recursiveTransferWeight_node sys F cut n x t P hv]
      change (cutc x t.1 _ _ : ℂ) *
        recursiveTransferWeight sys F cutc n ⟨n, _, _, _⟩ t.2.1 *
        star (recursiveTransferWeight sys F cutc n ⟨n, _, _, _⟩ t.2.2) = _
      simp only [ite_true, if_true, Bool.false_eq_true, ite_false, if_false]
      rw [hl, hr]
      have hc : cutc x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
          (x.compensation value : ℝ) * cut x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) :=
        movingSlotCutoff_compensated value childBound pivotBound E x _ _ _
      rw [hc]
      simp only [movingSampleProduct, Complex.ofReal_mul, Complex.ofReal_natCast,
        Nat.cast_mul, star_mul, star_natCast]
      change _ = (x.compensation value : ℂ) * _ * _ * _
      simp only [sys, movingSlotSystem, MovingSlotState.child, x, buildMovingSlotData,
        ite_true, if_true, Bool.false_eq_true, ite_false, if_false]
      ring
    · have hz₁ : recursiveTransferWeight sys F cutc (n + 1) x t = 0 := by
        simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
      have hz₂ : recursiveTransferWeight sys F cut (n + 1) x t = 0 := by
        simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
      rw [hz₁, hz₂, mul_zero]

theorem movingSupportedWeight_mul {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (c z : ℂ) :
    movingSupportedWeight value outside T XL XR (c * z) =
      c * movingSupportedWeight value outside T XL XR z := by
  unfold movingSupportedWeight
  split_ifs <;> simp only [mul_zero]

/-- Exact compensated prior times the supported coefficient with node
compensations removed. This is the scalar used by the pattern comparison. -/
theorem movingSampledWeight_compensated_supported {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
      (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))
      n t small bulk XL XR =
      ∑ a : MovingSampleSlots σ n,
        (((movingSampleProduct value a : ℝ) * movingSamplesPrior μ a : ℝ) : ℂ) *
          movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
            (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
              (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
              ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t) := by
  rw [movingSampledWeight_supported]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingLocalExtra_compensated, movingRecursiveWeight_compensated,
    movingSupportedWeight_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePairExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact paired expansion of the fully supported sampled coefficient

The equality-pattern scalar is the literal original prior times all node
compensations. The remaining coefficient retains every support test.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSupportedSampledWeight_eq {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small bulk XL XR =
      movingCompensatedAverage μ value n
        (movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR) :=
  movingSampledWeight_compensated_supported value outside μ childBound pivotBound F E n t small bulk XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalSampleExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original Fourier coefficient under the exact internal sampling law -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalNode_local {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    movingLocalExtra (movingOriginalNode value childBound pivotBound φ G) =
      movingOriginalNode value childBound pivotBound φ G := by
  funext x s v w
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeRowTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant-only prime-to-integer row transfer in Section 7.5

The compensation product stays in the modulus. Only the actual giant prime
is averaged with its smooth harmonic prior, so no tuple-factorial loss occurs.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem moving_prime_row_transfer {A : Type*} [Fintype A]
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hμmass : ∑ a, μ a = 1)
    (w : ℕ → ℝ) (hw : ∀ p ∈ I, 0 ≤ w p) (Z : ℝ) (hZ : 0 ≤ Z)
    (hmass : ∑ p : P, Z * w p / (p : ℝ) = 1)
    (U : A → ℕ)
    (row : ∀ a, (p : P) → Fin ((p : ℕ) * U a) → ℂ)
    (B : ∀ a p, Fin (p * U a) → ℂ)
    (hrow : ∀ a p, (∑ t, ‖row a p t‖ ^ 2) ≤ (p : ℕ) * (U a : ℝ)) :
    ‖∑ a, (μ a : ℂ) * ∑ p : P, ((Z * w p / (p : ℝ) : ℝ) : ℂ) *
        ∑ t, row a p t * B a p t‖ ^ 2 ≤
      Z * ∑ a, μ a * (U a : ℝ) * ∑ p ∈ I, w p * ∑ t, ‖B a p t‖ ^ 2 := by
  let ν := fun ap : A × P => μ ap.1 * (Z * w ap.2 / (ap.2 : ℝ))
  have hν (ap) : 0 ≤ ν ap :=
    mul_nonneg (hμ ap.1) (div_nonneg (mul_nonneg hZ (hw _ (hPI ap.2.property)))
      (Nat.cast_nonneg _))
  have hνmass : ∑ ap, ν ap = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [ν, ← Finset.mul_sum, hmass, mul_one, hμmass]
  have hh := finite_transfer_row_bound ν hν hνmass
    (fun ap => row ap.1 ap.2) (fun ap => B ap.1 ap.2)
    (fun ap => (ap.2 : ℕ) * (U ap.1 : ℝ)) (fun ap => hrow ap.1 ap.2)
  have hleft : (∑ ap : A × P, (ν ap : ℂ) * ∑ t, row ap.1 ap.2 t * B ap.1 ap.2 t) =
      ∑ a, (μ a : ℂ) * ∑ p : P, ((Z * w p / (p : ℝ) : ℝ) : ℂ) *
        ∑ t, row a p t * B a p t := by
    rw [Fintype.sum_prod_type]
    simp only [ν, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]
  rw [hleft] at hh
  apply hh.trans
  have hcancel (a) (p : P) :
      (Z * w p / (p : ℝ)) * ((p : ℕ) * (U a : ℝ)) = Z * (U a : ℝ) * w p := by
    have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hP _ p.property).ne_zero
    field_simp
  rw [Fintype.sum_prod_type]
  calc
    (∑ a, ∑ p : P, ν (a, p) * ((p : ℕ) * (U a : ℝ) * ∑ t, ‖B a p t‖ ^ 2)) =
        Z * ∑ a, μ a * (U a : ℝ) * ∑ p ∈ P, w p * ∑ t, ‖B a p t‖ ^ 2 := by
      simp only [ν]
      simp_rw [show ∀ a (p : P), μ a * (Z * w p / (p : ℝ)) *
          ((p : ℕ) * (U a : ℝ) * ∑ t, ‖B a p t‖ ^ 2) =
          Z * (μ a * (U a : ℝ) * (w p * ∑ t, ‖B a p t‖ ^ 2)) from fun a p => by
            calc
              _ = μ a * ((Z * w p / (p : ℝ)) * ((p : ℕ) * (U a : ℝ))) *
                  (∑ t, ‖B a p t‖ ^ 2) := by ring
              _ = _ := by rw [hcancel]; ring]
      simp only [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      simpa only [finite_univ_canonical] using
        (Finset.sum_coe_sort P (fun p => w p * ∑ t, ‖B a p t‖ ^ 2))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hZ
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hμ a) (Nat.cast_nonneg _))
      apply Finset.sum_le_sum_of_subset_of_nonneg hPI
      intro p hp _
      exact mul_nonneg (hw p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeArithmeticTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted giant-only integer substitution of Section 7.5 -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The exact weighted off-diagonal, with the original coefficient support
and without any multiplicity factor in the integer substitution. -/
theorem movingGiantOffDiagonal_eq {A : Type*} [Fintype A]
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p) (U : ℕ) (hU : 0 < U)
    (B H V : ℕ) (L : A → ℕ) (v : A → ℤ) (w : ℕ → ℝ) (c : ℕ → A → ℂ)
    (hv : ∀ p ∈ I, ∀ a, c p a ≠ 0 → (v a).natAbs ≤ B)
    (hL : ∀ p ∈ I, ∀ a, c p a ≠ 0 → L a ≤ H)
    (hscale : ∀ p ∈ I, 2 * B * H ≤ V * (p * U)) :
    (∑ p ∈ I, (w p : ℂ) * pivotOffDiagonal (p * U) L v (c p)) =
      movingGiantOffDiagonal I V U L v w c := by
  have hUnz : (U : ℤ) ≠ 0 := by exact_mod_cast hU.ne'
  have he (p : ℕ) (s : ℤ) (a b : A) :
      (s ≠ 0 ∧ v a * L b - v b * L a = s * ((p * U : ℕ) : ℤ)) ↔
      (s * (U : ℤ) ≠ 0 ∧ v a * L b - v b * L a = (s * U) * p) := by
    have hmul : s * ((p * U : ℕ) : ℤ) = (s * U) * p := by push_cast; ring
    rw [hmul]
    constructor
    · rintro ⟨hs, hh⟩
      exact ⟨mul_ne_zero hs hUnz, hh⟩
    · rintro ⟨hs, hh⟩
      exact ⟨left_ne_zero_of_mul hs, hh⟩
  calc
    _ = ∑ p ∈ I, ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
        if s * (U : ℤ) ≠ 0 ∧ v a * L b - v b * L a = (s * U) * p
        then (w p : ℂ) * c p a * conj (c p b) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [pivotOffDiagonal_frequency_on_support (p * U) B H V
        (Nat.mul_pos (hI p hp) hU) L v (c p) (hv p hp) (hL p hp) (hscale p hp)]
      simp only [Finset.mul_sum, mul_ite, mul_zero]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [he p s a b, mul_assoc]
    _ = movingGiantOffDiagonal I V U L v w c := by
      unfold movingGiantOffDiagonal
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      exact transferred_pivot_substitution I hI _ (s * U)
        (fun p => (w p : ℂ) * c p a * conj (c p b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRootReconstruction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integer substitution is the giant in the original node coefficient -/

namespace Ostmann
open scoped Classical

/-- The composite pivot reconstructed by the history system is the
compensation product times the reconstructed giant. -/
theorem reconstructedPivot_compensation (I : Finset ℕ) (N s : ℤ) (U : ℕ)
    (h : validTransferredPivot I N (s * U)) :
    reconstructedPivot N s = reconstructedPivot N (s * U) * U := by
  have hs : s ≠ 0 := left_ne_zero_of_mul h.1
  have he := validTransferredPivot_equation I N (s * U) h
  apply reconstructedPivot_of_eq N s hs
  push_cast
  calc
    N = (s * U) * reconstructedPivot N (s * U) := he
    _ = _ := by ring

theorem reconstructedGiant_eq_div (I : Finset ℕ) (N s : ℤ) (U : ℕ)
    (hU : 0 < U) (h : validTransferredPivot I N (s * U)) :
    reconstructedPivot N s / U = reconstructedPivot N (s * U) := by
  rw [reconstructedPivot_compensation I N s U h, Nat.mul_div_left _ hU]

/-- Conversely the original composite-pivot integrality test gives exactly
one positive giant in the retained integer range. -/
theorem validTransferredGiant_of_composite (I : Finset ℕ)
    (N s : ℤ) (P U : ℕ) (hs : s ≠ 0) (hP : 0 < P) (hU : 0 < U)
    (hdiv : U ∣ P) (hI : P / U ∈ I) (hrel : N = s * P) :
    validTransferredPivot I N (s * U) := by
  have he : P / U * U = P := Nat.div_mul_cancel hdiv
  have hp : 0 < P / U := by
    by_contra hn
    have hz : P / U = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz, zero_mul] at he
    omega
  apply validTransferredPivot_of_eq I N (s * U)
    (mul_ne_zero hs (by exact_mod_cast hU.ne')) (P / U) hp hI
  calc
    N = s * (P : ℤ) := hrel
    _ = s * (((P / U) * U : ℕ) : ℤ) := by rw [he]
    _ = (s * (U : ℤ)) * ((P / U : ℕ) : ℤ) := by rw [Nat.cast_mul]; ring

/-- The node's original factor is exactly `U φ(log p - G)`, where `p` is
reconstructed from the same signed quotient as the integer off-diagonal. -/
theorem movingOriginalNode_reconstructed {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (x : MovingSlotState σ) (s v w : ℤ)
    (hU : 0 < x.compensation value)
    (h : validTransferredPivot I
      (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ))
      (s * x.compensation value)) :
    movingSlotCutoff value childBound pivotBound
      (movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G))
        x s v w =
      (x.compensation value : ℝ) * φ
        (Real.log (reconstructedPivot
          (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ))
          (s * x.compensation value)) - G x.depth) := by
  let N := v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)
  let U := x.compensation value
  let p := reconstructedPivot N (s * U)
  have hP : historyPivot (movingSlotSystem value childBound pivotBound) x s v w = p * U :=
    reconstructedPivot_compensation I N s U h
  have hdiv : U ∣ historyPivot (movingSlotSystem value childBound pivotBound) x s v w := by
    rw [hP]
    exact dvd_mul_left U p
  have hquot : historyPivot (movingSlotSystem value childBound pivotBound) x s v w / U = p := by
    rw [hP, Nat.mul_div_left _ hU]
  have hp : 0 < (p : ℝ) := by exact_mod_cast hI p h.2.2.2
  unfold movingSlotCutoff
  rw [ite_eq_left ⟨hU, hdiv⟩]
  change (U : ℝ) * (1 * positiveLogCutoff φ (G x.depth)
    (historyPivot (movingSlotSystem value childBound pivotBound) x s v w / U : ℕ)) = _
  rw [hquot, one_mul, positiveLogCutoff, ite_eq_left hp]

/-- An unconditional node formula in terms of the reconstructed giant.
All original frequency, range, and coprimality tests remain in the guard. -/
theorem movingSampleRootFactor_reconstructed {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (t : FrequencyTree ℤ (n + 1)) (CL CR u : List σ) (XL XR : ℕ) :
    let x := movingRootState n t CL CR u XL XR
    let sys := movingSlotSystem value childBound pivotBound
    let v := frequencyRoot n t.2.1
    let w := frequencyRoot n t.2.2
    let U := x.compensation value
    let p := reconstructedPivot (v * (x.rightProduct value : ℤ) -
      w * (x.leftProduct value : ℤ)) (t.1 * U)
    movingSampleRootFactor value childBound pivotBound
      (movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G))
        n t CL CR u XL XR =
      if ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U then
        ((U : ℝ) * φ (Real.log p - G (n + 1)) : ℂ) else 0 := by
  dsimp only
  let x := movingRootState n t CL CR u XL XR
  let sys := movingSlotSystem value childBound pivotBound
  let v := frequencyRoot n t.2.1
  let w := frequencyRoot n t.2.2
  let U := x.compensation value
  let N := v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)
  let p := reconstructedPivot N (t.1 * U)
  let P := historyPivot sys x t.1 v w
  change (if ValidTransferNode sys x t.1 v w P then
    (movingSlotCutoff value childBound pivotBound
      (movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G))
      x t.1 v w : ℂ) else 0) =
    if ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U then
      ((U : ℝ) * φ (Real.log p - G (n + 1)) : ℂ) else 0
  by_cases h : ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U
  · have hP : P = p * U := h.1.historyPivot_eq
    have hp : 0 < p := Nat.pos_of_mul_pos_right h.1.pivot_pos
    have he : N = (t.1 * (U : ℤ)) * p := by
      have hh := h.1.relation
      change N = t.1 * ((p * U : ℕ) : ℤ) at hh
      rw [Nat.cast_mul] at hh
      calc
        N = t.1 * ((p : ℤ) * U) := hh
        _ = _ := by ring
    have hvalid : validTransferredPivot {p} N (t.1 * U) :=
      validTransferredPivot_of_eq {p} N (t.1 * U)
        (mul_ne_zero h.1.root_ne_zero (by exact_mod_cast h.2.ne')) p hp (by simp) he
    have hcut := movingOriginalNode_reconstructed value childBound pivotBound φ G
      {p} (fun q hq => by simpa only [Finset.mem_singleton.mp hq] using hp)
      x t.1 v w h.2 hvalid
    rw [ite_eq_left h, hP, ite_eq_left h.1, hcut]
    simp only [Complex.ofReal_mul]
    rfl

  · rw [ite_eq_right h]
    by_cases hv : ValidTransferNode sys x t.1 v w P
    · rw [ite_eq_left hv]
      have hdiv : ¬(0 < U ∧ U ∣ P) := by
        rintro ⟨hU, hd⟩
        have hh := validTransferredGiant_of_composite {P / U} N t.1 P U
          hv.root_ne_zero hv.pivot_pos hU hd (by simp) hv.relation
        have he : P / U = p := (reconstructedGiant_eq_div {P / U} N t.1 U hU hh)
        have hPU : P = p * U := by rw [← he]; exact (Nat.div_mul_cancel hd).symm
        exact h ⟨hPU ▸ hv, hU⟩
      change ((if 0 < U ∧ U ∣ P then _ else 0 : ℝ) : ℂ) = 0
      rw [ite_eq_right hdiv, Complex.ofReal_zero]
    · rw [ite_eq_right hv]

/-- The full current-state support guard commutes with root extraction.
Its subtree-frequency unit tests are not discarded by the integer change
of variables. -/
theorem movingSampleRootFactor_guarded {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (n : ℕ)
    (t : FrequencyTree ℤ (n + 1)) (CL CR u : List σ) (XL XR : ℕ) :
    movingSampleRootFactor value childBound pivotBound (movingGuardedExtra value outside E)
      n t CL CR u XL XR =
      if movingLocalSupport value outside (movingRootState n t CL CR u XL XR) then
        movingSampleRootFactor value childBound pivotBound E n t CL CR u XL XR else 0 := by
  unfold movingSampleRootFactor
  dsimp only
  rw [movingSlotCutoff_guarded]
  split_ifs <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGuardedDirectRecursion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fully guarded sampled recursion with the explicit giant quotient -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original sample law and the two independent child sample trees are
retained. The inserted giant is exactly `(v H⁻ - w H⁺)/(s U)`, matching the
weighted integer off-diagonal, with every root support test still explicit. -/
theorem movingSampledWeight_guarded_direct_node {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ) :
    let E := movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G)
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) (n + 1) t small bulk XL XR =
      ∑ a : TreeLeafTuple (Fin 4 → σ) n,
        let u := movingCompensationSlots n a
        let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
        let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
        let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
        let U := x.compensation value
        let v := frequencyRoot n t.2.1
        let w := frequencyRoot n t.2.2
        let p := reconstructedPivot
          (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)) (t.1 * U)
        (movingCompensationPrior (μ n) n a : ℂ) *
          if movingLocalSupport value outside x ∧
              (ValidTransferNode (movingSlotSystem value childBound pivotBound) x t.1 v w (p * U) ∧
                0 < U) then
            (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
              movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.1
                (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
              star (movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.2
                (appendMovingSlotLeaves n u small.2) bulk.2 p XR)
          else 0 := by
  intro E
  rw [movingSampledWeight_node]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  let u := movingCompensationSlots n a
  let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
  let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
  let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
  let U := x.compensation value
  let sys := movingSlotSystem value childBound pivotBound
  let v := frequencyRoot n t.2.1
  let w := frequencyRoot n t.2.2
  let P := historyPivot sys x t.1 v w
  let p := reconstructedPivot (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)) (t.1 * U)
  have hbase := movingSampleRootFactor_reconstructed value childBound pivotBound φ G n t
    CL CR (flattenMovingSlots n u) XL XR
  dsimp only at hbase
  simp only [← Complex.ofReal_mul] at hbase
  have hguard := movingSampleRootFactor_guarded value outside childBound pivotBound E n t
    CL CR (flattenMovingSlots n u) XL XR
  rw [hbase] at hguard
  change movingSampleRootFactor value childBound pivotBound
      (movingGuardedExtra value outside E) n t CL CR (flattenMovingSlots n u) XL XR =
    (if movingLocalSupport value outside x then
      (if ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) else 0) else 0) at hguard
  have hroot : movingSampleRootFactor value childBound pivotBound
      (movingGuardedExtra value outside E) n t CL CR (flattenMovingSlots n u) XL XR =
      if movingLocalSupport value outside x ∧
          (ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U) then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) else 0 := by
    rw [hguard]
    by_cases hl : movingLocalSupport value outside x
    · simp only [hl, true_and, ite_true, if_true]
    · simp only [hl, false_and, ite_false, if_false]
  change (movingCompensationPrior (μ n) n a : ℂ) *
      movingSampleRootFactor value childBound pivotBound (movingGuardedExtra value outside E) n t CL CR
        (flattenMovingSlots n u) XL XR *
      movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.1
        (appendMovingSlotLeaves n u small.1) bulk.1 (P / U) XL *
      star (movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.2
        (appendMovingSlotLeaves n u small.2) bulk.2 (P / U) XR) =
    (movingCompensationPrior (μ n) n a : ℂ) *
      (if movingLocalSupport value outside x ∧
          (ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U) then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
          movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.1
            (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
          star (movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.2
            (appendMovingSlotLeaves n u small.2) bulk.2 p XR)
        else 0)
  rw [hroot]
  by_cases h : movingLocalSupport value outside x ∧
      (ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U)
  · have hP : P = p * U := h.2.1.historyPivot_eq
    have hp : P / U = p := by rw [hP, Nat.mul_div_left _ h.2.2]
    rw [ite_eq_left h, ite_eq_left h, hp]
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    simp only [mul_zero, zero_mul]

/-- The same exact recurrence for the fully supported coefficient used by
the arithmetic comparison. -/
theorem movingSupportedSampledWeight_direct_node {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ) :
    let E := movingOriginalNode value childBound pivotBound φ G
    movingSupportedSampledWeight value outside μ childBound pivotBound F E (n + 1) t small bulk XL XR =
      ∑ a : TreeLeafTuple (Fin 4 → σ) n,
        let u := movingCompensationSlots n a
        let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
        let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
        let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
        let U := x.compensation value
        let v := frequencyRoot n t.2.1
        let w := frequencyRoot n t.2.2
        let p := reconstructedPivot
          (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)) (t.1 * U)
        (movingCompensationPrior (μ n) n a : ℂ) *
          if movingLocalSupport value outside x ∧
              (ValidTransferNode (movingSlotSystem value childBound pivotBound) x t.1 v w (p * U) ∧
                0 < U) then
            (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
              movingSupportedSampledWeight value outside μ childBound pivotBound F E n t.2.1
                (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
              star (movingSupportedSampledWeight value outside μ childBound pivotBound F E n t.2.2
                (appendMovingSlotLeaves n u small.2) bulk.2 p XR)
          else 0 := by
  dsimp only
  simpa only [movingSupportedSampledWeight, movingLocalExtra_compensated,
    movingOriginalNode_local] using
    movingSampledWeight_guarded_direct_node value outside μ childBound pivotBound F φ G
      n t small bulk XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual sampled coefficient over its internal frequencies -/

namespace Ostmann
open scoped Classical BigOperators

theorem scheduledFrequencyRootEquiv_history (V : ℕ → ℕ) (n : ℕ)
    (t : ScheduledFrequencyIndex V n) :
    scheduledFrequencyHistory V n t =
      movingRootedFrequencyTree V n (scheduledFrequencyRootEquiv V n t).1.val
        (scheduledFrequencyRootEquiv V n t).2 := by
  cases n <;> rfl

/-- At a successor level the two child histories are independent finite
indices, while each root compensation vector is shared exactly once. -/
theorem movingFrequencyCoefficient_node {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      (n + 1) s small bulk XL XR =
      ∑ l : ScheduledFrequencyIndex V n, ∑ r : ScheduledFrequencyIndex V n,
        ∑ a : TreeLeafTuple (Fin 4 → σ) n,
          let u := movingCompensationSlots n a
          let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
          let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
          let t := (s, scheduledFrequencyHistory V n l, scheduledFrequencyHistory V n r)
          let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
          let U := x.compensation value
          let v := frequencyRoot n t.2.1
          let w := frequencyRoot n t.2.2
          let p := reconstructedPivot
            (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)) (s * U)
          (movingCompensationPrior (μ n) n a : ℂ) *
            if movingLocalSupport value outside x ∧
                (ValidTransferNode (movingSlotSystem value childBound pivotBound) x s v w (p * U) ∧
                  0 < U) then
              (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
                movingSupportedSampledWeight value outside μ childBound pivotBound F
                  (movingOriginalNode value childBound pivotBound φ G) n t.2.1
                  (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
                star (movingSupportedSampledWeight value outside μ childBound pivotBound F
                  (movingOriginalNode value childBound pivotBound φ G) n t.2.2
                  (appendMovingSlotLeaves n u small.2) bulk.2 p XR)
            else 0 := by
  unfold movingFrequencyCoefficient
  change (∑ t : ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n, _) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  exact movingSupportedSampledWeight_direct_node value outside μ childBound pivotBound F φ G n
    (s, scheduledFrequencyHistory V n l, scheduledFrequencyHistory V n r) small bulk XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_MovingZeroFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Zero frequencies vanish in the original sampled histories -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem recursiveTransferWeight_nonzero_frequencies {State : Type*}
    (sys : TransferHistorySystem State) (leaf : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (hleaf : ∀ x, leaf x 0 = 0)
    (n : ℕ) (x : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  induction n generalizing x with
  | zero =>
    intro s hs
    have hst : s = t := by simpa only [allFrequencyList, List.mem_singleton] using hs
    subst s
    intro hz
    subst t
    exact ht (hleaf x)
  | succ n ih =>
    obtain ⟨P, hP, _, _⟩ := recursiveTransferWeight_nonzero_valid sys leaf cutoff _ x t ht
    rw [recursiveTransferWeight_node sys leaf cutoff n x t P hP] at ht
    have hL : recursiveTransferWeight sys leaf cutoff n (sys.leftState x P) t.2.1 ≠ 0 := by
      intro hz
      exact ht (by rw [hz, mul_zero, zero_mul])
    have hR : recursiveTransferWeight sys leaf cutoff n (sys.rightState x P) t.2.2 ≠ 0 := by
      intro hz
      exact ht (by rw [hz, star_zero, mul_zero])
    intro s hs
    simp only [allFrequencyList, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · exact hP.root_ne_zero
    · exact ih _ _ hL s hs
    · exact ih _ _ hR s hs

theorem movingSupportedSampledWeight_zero_frequency {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (hF : ∀ x, F x 0 = 0)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) (hz : ¬ ∀ s ∈ allFrequencyList n t, s ≠ 0) :
    movingSupportedSampledWeight value outside μ childBound pivotBound F E
      n t small bulk XL XR = 0 := by
  unfold movingSupportedSampledWeight movingSampledWeight
  apply Finset.sum_eq_zero
  intro a _
  suffices h : recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingGuardedLeaf value outside F)
      (movingSlotCutoff value childBound pivotBound
        (movingLocalExtra
          (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))))
      n ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t = 0 by
    rw [h, mul_zero]
  by_contra hn
  apply hz
  apply recursiveTransferWeight_nonzero_frequencies _ _ _ _ n _ t hn
  intro x
  simp only [movingGuardedLeaf, hF, ite_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's normalized residue indicators and additive transforms -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem residueVariance_pos {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) : 0 < residueVariance S := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hd : 0 < residueDensity S := div_pos (by exact_mod_cast hS.card_pos) hp
  have hd1 : residueDensity S < 1 := (div_lt_one hp).mpr (by exact_mod_cast hSp)
  exact mul_pos hd (sub_pos.mpr hd1)

theorem centeredDensity_sq_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, centeredDensity S x ^ 2) = (p : ℝ) * residueVariance S := by
  let σ := residueDensity S
  have hsq (x : ZMod p) : centeredDensity S x ^ 2 =
      (if x ∈ S then 1 - 2 * σ else 0) + σ ^ 2 := by
    dsimp [centeredDensity, σ, residueDensity]
    split <;> ring
  simp_rw [hsq]
  rw [Finset.sum_add_distrib]
  have hsum : (∑ x : ZMod p, if x ∈ S then (1 - 2 * σ) else 0) = S.card * (1 - 2 * σ) := by simp; ring
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hσ : (p : ℝ) * σ = S.card := by dsimp [σ, residueDensity]; field_simp
  change _ = (p : ℝ) * (σ * (1 - σ))
  rw [← hσ]
  ring

theorem normalizedResidueIndicator_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueIndicator S x‖ ^ 2) = p := by
  have hv := residueVariance_pos S hS hSp
  simp only [normalizedResidueIndicator, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    div_pow, ← Finset.sum_div, Real.sq_sqrt hv.le, centeredDensity_sq_sum]
  exact mul_div_cancel_right₀ (p : ℝ) hv.ne'

theorem normalizedResidueTransform_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueTransform S x‖ ^ 2) = p := by
  rw [normalizedResidueTransform, densityFourier_energy, normalizedResidueIndicator_energy S hS hSp]

theorem normalizedResidueTransform_neg {p : ℕ} [Fact p.Prime] (S : Finset (ZMod p)) (x : ZMod p) :
    normalizedResidueTransform S (-x) = conj (normalizedResidueTransform S x) := by
  have hreal : (fun y => conj (normalizedResidueIndicator S y)) = normalizedResidueIndicator S := by
    funext y
    simp only [normalizedResidueIndicator, Complex.conj_ofReal]
  have hh := additiveFourier_conj (normalizedResidueIndicator S) (-x)
  rw [hreal, neg_neg] at hh
  simp only [normalizedResidueTransform, densityFourier, map_mul, Complex.conj_ofReal]
  rw [hh]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFormulaRenaming
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the polynomial support bound onto actual finite prime slots -/

namespace Ostmann

open scoped BigOperators Classical

theorem finite_prior_reindex {V W A : Type*} [Fintype V] [Fintype W] [Fintype A]
    (e : V ≃ W) (μ : W → A → ℝ) (F : (W → A) → ℂ) :
    (∑ x : V → A, ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm)) =
      ∑ x : W → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x := by
  have he := (Equiv.arrowCongr e (Equiv.refl A)).sum_comp
    (fun x : W → A => ((∏ i, μ i (x i) : ℝ) : ℂ) * F x)
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  change ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm) =
    ((∏ i, μ i (x (e.symm i)) : ℝ) : ℂ) * F (x ∘ e.symm)
  congr 2
  simpa only [Equiv.symm_apply_apply] using
    e.prod_comp (fun i => μ i (x (e.symm i)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving regular Fourier transform in the giant-only transfer -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

private theorem transfer_quotient {K : Type*} [Field K]
    (P R D v s : K) (hP : P ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (h : v * R = s * P) : v / (P * D) = s / (R * D) := by
  apply (div_eq_div_iff (mul_ne_zero hP hD) (mul_ne_zero hR hD)).mpr
  calc
    v * (R * D) = (v * R) * D := by ring
    _ = (s * P) * D := by rw [h]
    _ = s * (P * D) := by ring

/-- The local left transform keeps its function; only the denominator changes. -/
theorem moving_regular_left_transfer {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (L R M D : ℕ) (v w s : ℤ)
    (hpL : p ∣ L) (hM : M.Coprime p) (hR : R.Coprime p) (hD : D.Coprime p)
    (hrel : v * R - w * L = s * M) :
    g ((v : ZMod p) / ((M * D : ℕ) : ZMod p)) =
      g ((s : ZMod p) / ((R * D : ℕ) : ZMod p)) := by
  congr 1
  simp only [Nat.cast_mul]
  exact transfer_quotient _ _ _ _ _
    (zmod_natCast_ne_zero_of_coprime M hM)
    (zmod_natCast_ne_zero_of_coprime R hR)
    (zmod_natCast_ne_zero_of_coprime D hD)
    (transfer_equation_mod_left p L R M v w s hpL hrel)

/-- The conjugated right transform has the same new argument, because the
underlying physical residue function is real. -/
theorem moving_regular_right_transfer {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : ∀ x, g (-x) = conj (g x))
    (L R M D : ℕ) (v w s : ℤ)
    (hpR : p ∣ R) (hM : M.Coprime p) (hL : L.Coprime p) (hD : D.Coprime p)
    (hrel : v * R - w * L = s * M) :
    conj (g ((w : ZMod p) / ((M * D : ℕ) : ZMod p))) =
      g ((s : ZMod p) / ((L * D : ℕ) : ZMod p)) := by
  rw [← hg]
  congr 1
  simp only [Nat.cast_mul, ← neg_div]
  exact transfer_quotient _ _ _ _ _
    (zmod_natCast_ne_zero_of_coprime M hM)
    (zmod_natCast_ne_zero_of_coprime L hL)
    (zmod_natCast_ne_zero_of_coprime D hD)
    (transfer_equation_mod_right p L R M v w s hpR hrel)

/-- The extracted row depends only on the grouped key `v/H mod P`, with
the original outside denominator and every local cofactor unchanged. -/
theorem moving_regular_transform_grouped_key {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (g : ∀ j, ZMod (p j) → ℂ) (H D : ℕ) (v : ℤ)
    (hH : H.Coprime (∏ j, p j)) :
    movingRegularTransform p g D
      ((positiveIntegerPivotKey (∏ j, p j)
        (Finset.prod_pos (fun j _ => (Fact.out : (p j).Prime).pos)) H v).val : ℤ) =
      movingRegularTransform p g (D * H) v := by
  unfold movingRegularTransform
  apply Finset.prod_congr rfl
  intro j _
  have hd := Finset.dvd_prod_of_mem p (Finset.mem_univ j)
  have hHj := zmod_natCast_ne_zero_of_coprime H (hH.of_dvd_right hd)
  have he := positiveIntegerPivotKey_mul_at_divisor (∏ j, p j)
    (Finset.prod_pos (fun j _ => (Fact.out : (p j).Prime).pos)) H v hd hH
  have heq := (eq_div_iff hHj).mpr he
  simp only [Int.cast_natCast, heq, div_eq_mul_inv, Nat.cast_mul, mul_inv_rev]
  congr 1
  ring

attribute [local instance] OAI.Ostmann.sumElim_neZero
/-- No averaging or approximation occurs when the two surviving transforms
combine. The extracted pivot and compensation product disappear together. -/
theorem moving_regular_transform_transfer {H K : Type*} [Fintype H] [Fintype K]
    (L : H → ℕ) (R : K → ℕ)
    [∀ i, Fact (L i).Prime] [∀ i, Fact (R i).Prime]
    (gL : ∀ i, ZMod (L i) → ℂ) (gR : ∀ i, ZMod (R i) → ℂ)
    (hgR : ∀ i x, gR i (-x) = conj (gR i x))
    (M D : ℕ) (v w s : ℤ)
    (hc : Pairwise (fun i j => (Sum.elim L R i).Coprime (Sum.elim L R j)))
    (hM : ∀ i, M.Coprime (Sum.elim L R i))
    (hD : ∀ i, D.Coprime (Sum.elim L R i))
    (hrel : v * (∏ i, R i) - w * (∏ i, L i) = s * M) :
    movingRegularTransform L gL (M * D) v *
      conj (movingRegularTransform R gR (M * D) w) =
    movingRegularTransform (Sum.elim L R)
      (fun i => match i with | .inl j => gL j | .inr j => gR j) D s := by
  have hLc : Pairwise (fun i j => (L i).Coprime (L j)) := by
    intro i j hij
    exact hc (by simpa using hij : Sum.inl i ≠ Sum.inl j)
  have hRc : Pairwise (fun i j => (R i).Coprime (R j)) := by
    intro i j hij
    exact hc (by simpa using hij : Sum.inr i ≠ Sum.inr j)
  have hleft (i : H) :
      gL i ((v : ZMod (L i)) / ((M * D * tupleCofactor L i : ℕ) : ZMod (L i))) =
      gL i ((s : ZMod (L i)) /
        ((D * tupleCofactor (Sum.elim L R) (.inl i) : ℕ) : ZMod (L i))) := by
    have hRi : (∏ j, R j).Coprime (L i) := Nat.coprime_prod_left_iff.mpr (by
      intro j _
      exact hc (by simp : Sum.inr j ≠ Sum.inl i))
    have hh := moving_regular_left_transfer (gL i) (∏ j, L j) (∏ j, R j) M
      (D * tupleCofactor L i) v w s (Finset.dvd_prod_of_mem L (Finset.mem_univ i))
      (hM (.inl i)) hRi ((hD (.inl i)).mul_left (tupleCofactor_coprime L hLc i)) hrel
    simpa only [tupleCofactor_sum_left L R i (Fact.out : (L i).Prime).ne_zero,
      mul_assoc, mul_left_comm, mul_comm] using hh
  have hright (i : K) :
      conj (gR i ((w : ZMod (R i)) / ((M * D * tupleCofactor R i : ℕ) : ZMod (R i)))) =
      gR i ((s : ZMod (R i)) /
        ((D * tupleCofactor (Sum.elim L R) (.inr i) : ℕ) : ZMod (R i))) := by
    have hLi : (∏ j, L j).Coprime (R i) := Nat.coprime_prod_left_iff.mpr (by
      intro j _
      exact hc (by simp : Sum.inl j ≠ Sum.inr i))
    have hh := moving_regular_right_transfer (gR i) (hgR i) (∏ j, L j) (∏ j, R j) M
      (D * tupleCofactor R i) v w s (Finset.dvd_prod_of_mem R (Finset.mem_univ i))
      (hM (.inr i)) hLi ((hD (.inr i)).mul_left (tupleCofactor_coprime R hRc i)) hrel
    simpa only [tupleCofactor_sum_right L R i (Fact.out : (R i).Prime).ne_zero,
      mul_assoc, mul_left_comm, mul_comm] using hh
  unfold movingRegularTransform
  rw [map_prod, Fintype.prod_sum_type]
  simp only [div_eq_mul_inv] at hleft hright
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl (fun i _ => hleft i))
    (Finset.prod_congr rfl (fun i _ => hright i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem complexUnitPhase_norm_le (z : ℂ) : ‖complexUnitPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [complexUnitPhase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    rw [div_self (norm_ne_zero_iff.mpr hz)]

theorem complexUnitPhase_conj (z : ℂ) :
    complexUnitPhase (conj z) = conj (complexUnitPhase z) := by
  simp only [complexUnitPhase, Complex.norm_conj, map_div₀, Complex.conj_ofReal]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact smooth harmonic giant prior from (7.3) -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrior_mass (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (hpos : 0 < smoothGiantMass P φ G) : ∑ p : P, smoothGiantPrior P φ G p = 1 := by
  have hs : (∑ p : P, φ (Real.log p - G) / (p : ℝ)) = smoothGiantMass P φ G := by
    simpa only [finite_univ_canonical, smoothGiantMass] using
      (Finset.sum_coe_sort P (fun p => φ (Real.log p - G) / (p : ℝ)))
  simp only [smoothGiantPrior, mul_div_assoc, ← Finset.mul_sum]
  rw [hs, smoothGiantLogNormalizer, Real.exp_neg, Real.exp_log hpos]
  exact inv_mul_cancel₀ hpos.ne'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTransferSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support inherited by the reconstructed giant-only transfer -/

namespace Ostmann
open scoped Classical

/-- The two branch priors already supply their internal and outside tests.
The only new pairwise requirement is the cross-product coprimality. -/
theorem pairwise_coprime_merge_shared (A B Y : List ℕ)
    (hA : (A ++ Y).Pairwise Nat.Coprime)
    (hB : (B ++ Y).Pairwise Nat.Coprime) (hAB : A.prod.Coprime B.prod) :
    (A ++ B ++ Y).Pairwise Nat.Coprime := by
  obtain ⟨hAA, hYY, hAY⟩ := List.pairwise_append.mp hA
  obtain ⟨hBB, _, hBY⟩ := List.pairwise_append.mp hB
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_append.mpr ⟨hAA, hBB, ?_⟩, hYY, ?_⟩
  · intro a ha b hb
    exact (Nat.coprime_list_prod_right_iff.mp
      (Nat.coprime_list_prod_left_iff.mp hAB a ha)) b hb
  · intro a ha y hy
    rcases List.mem_append.mp ha with ha | ha
    · exact hAY a ha y hy
    · exact hBY a ha y hy

/-- All current giant tests, including descendant frequencies, follow from
pairwise support and the same large-prime separation used at the root. -/
theorem moving_local_support_of_large {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ)
    (hp : (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime)
    (hf : T.Frequencies (fun s => s ≠ 0 ∧
      ∀ q, q.Prime → q ∣ XL * XR → s.natAbs < q)) :
    movingLocalSupport value outside ⟨n, T, XL, XR⟩ := by
  have cast_coprime {a b : ℕ} (h : a.Coprime b) : IsCoprime (a : ℤ) (b : ℤ) := by
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by simpa only [Int.gcd_natCast_natCast] using h)
  have giant_frequency (X : ℕ) (hX : X ∣ XL * XR) :
      IsCoprime (X : ℤ) T.frequencyProduct := by
    apply (T.frequencies_isCoprime (X : ℤ)).mp
    apply hf.mono
    intro s hs
    have hu := large_prime_factors_coprime_frequency X s hs.1
      (fun q hq hqd => hs.2 q hq (hqd.trans hX))
    simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using hu
  have hXL := giant_frequency XL (dvd_mul_right XL XR)
  have hXR := giant_frequency XR (dvd_mul_left XR XL)
  have hpair := hp
  change (XL :: XR :: (T.regularSlots.map value ++ outside)).Pairwise Nat.Coprime at hpair
  obtain ⟨hL, htail⟩ := List.pairwise_cons.mp hpair
  obtain ⟨hR, _⟩ := List.pairwise_cons.mp htail
  have hLreg : XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) := by
    apply Nat.coprime_list_prod_right_iff.mpr
    intro a ha
    exact hL a (List.mem_cons_of_mem XR (List.mem_append_left outside ha))
  have hRreg : XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) := by
    apply Nat.coprime_list_prod_right_iff.mpr
    intro a ha
    exact hR a (List.mem_append_left outside ha)
  have hLout : XL.Coprime outside.prod := Nat.coprime_list_prod_right_iff.mpr
    (fun a ha => hL a (List.mem_cons_of_mem XR (List.mem_append_right _ ha)))
  have hRout : XR.Coprime outside.prod := Nat.coprime_list_prod_right_iff.mpr
    (fun a ha => hR a (List.mem_append_right _ ha))
  exact ⟨hp, hXL, hXR, cast_coprime hLreg, cast_coprime hRreg,
    cast_coprime hLout, cast_coprime hRout⟩

/-- In the transfer application the surviving top giants are actual primes.
All the additional descendant-frequency tests are therefore automatic. -/
theorem moving_local_support_prime_giants {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR V : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime) (hVL : V < XL) (hVR : V < XR)
    (hp : (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime)
    (hf : T.Frequencies (fun s => s ≠ 0 ∧ s.natAbs ≤ V)) :
    movingLocalSupport value outside ⟨n, T, XL, XR⟩ := by
  apply moving_local_support_of_large value outside T XL XR hp
  apply hf.mono
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro q hq hd
  rcases hq.dvd_mul.mp hd with hd | hd
  · have he : q = XL := ((Nat.dvd_prime hXL).mp hd).resolve_left hq.ne_one
    exact he ▸ hs.2.trans_lt hVL
  · have he : q = XR := ((Nat.dvd_prime hXR).mp hd).resolve_left hq.ne_one
    exact he ▸ hs.2.trans_lt hVR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeRootGuard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top frequency guards at actual prime giants -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotData.Follows.frequencies {σ : Type*} {n : ℕ}
    {T : MovingSlotData σ n} {t : FrequencyTree ℤ n} (hT : T.Follows t)
    (P : ℤ → Prop) (h : ∀ s ∈ allFrequencyList n t, P s) : T.Frequencies P := by
  induction T with
  | leaf s regular => exact h s (by simpa only [allFrequencyList, hT, List.mem_singleton])
  | node s CL CR U left right ihL ihR =>
    refine ⟨h s (by simp only [allFrequencyList, List.mem_cons, hT.1, true_or]), ?_, ?_⟩
    · exact ihL hT.2.1 (fun a ha => h a (List.mem_cons_of_mem _ (List.mem_append_left _ ha)))
    · exact ihR hT.2.2 (fun a ha => h a (List.mem_cons_of_mem _ (List.mem_append_right _ ha)))

theorem movingFrequencySkeleton_follows (σ : Type*) (n : ℕ) (t : FrequencyTree ℤ n) :
    (movingFrequencySkeleton σ n t).Follows t := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨rfl, ih t.2.1, ih t.2.2⟩

theorem movingRootState_prime_support_iff {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (CL CR U : List σ) (XL XR V : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime) (hVL : V < XL) (hVR : V < XR)
    (hf : ∀ s ∈ allFrequencyList (n + 1) t, s ≠ 0 ∧ s.natAbs ≤ V) :
    movingLocalSupport value outside (movingRootState n t CL CR U XL XR) ↔
      (XL :: XR :: ((CL ++ CR).map value ++ outside)).Pairwise Nat.Coprime := by
  constructor
  · exact fun h => h.1
  · intro hp
    apply moving_local_support_prime_giants value outside
      (movingRootState n t CL CR U XL XR).data XL XR V hXL hXR hVL hVR hp
    apply MovingSlotData.Follows.frequencies
      (T := (movingRootState n t CL CR U XL XR).data) (t := t) _ _ hf
    exact ⟨rfl, movingFrequencySkeleton_follows σ n t.2.1,
      movingFrequencySkeleton_follows σ n t.2.2⟩

/-- Nonzero child coefficients remove the zero-history cases. Thus the
remaining top guard depends only on the actual prime lists and the two root
frequencies, as required before the child sums are multiplied. -/
theorem movingRootState_prime_guard_product {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (hs : s ≠ 0) (hsV : s.natAbs ≤ V (n + 1))
    (l r : ScheduledFrequencyIndex V n)
    (small bulk : TreeLeafTuple (List σ) (n + 1))
    (a : TreeLeafTuple (Fin 4 → σ) n) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR) (C : ℂ) (guard : Prop) :
    let u := movingCompensationSlots n a
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let t := (s, scheduledFrequencyHistory V n l, scheduledFrequencyHistory V n r)
    let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
    let p := reconstructedPivot
      (frequencyRoot n t.2.1 * (x.rightProduct value : ℤ) -
        frequencyRoot n t.2.2 * (x.leftProduct value : ℤ)) (s * x.compensation value)
    let L := movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n t.2.1
      (appendMovingSlotLeaves n u small.1) bulk.1 p XL
    let R := movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n t.2.2
      (appendMovingSlotLeaves n u small.2) bulk.2 p XR
    (if movingLocalSupport value outside x ∧ guard then C * L * star R else 0) =
      (if (XL :: XR :: ((CL ++ CR).map value ++ outside)).Pairwise Nat.Coprime ∧ guard
        then C * L * star R else 0) := by
  dsimp only
  by_cases hl : ∀ z ∈ allFrequencyList n (scheduledFrequencyHistory V n l), z ≠ 0
  · by_cases hr : ∀ z ∈ allFrequencyList n (scheduledFrequencyHistory V n r), z ≠ 0
    · have hf : ∀ z ∈ allFrequencyList (n + 1)
          (s, scheduledFrequencyHistory V n l, scheduledFrequencyHistory V n r),
          z ≠ 0 ∧ z.natAbs ≤ V (n + 1) := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨hs, hsV⟩
        · rcases List.mem_append.mp hz with hz | hz
          · exact ⟨hl z hz, (scheduledFrequencyHistory_all_bound V hV n l z hz).trans
              (hV (Nat.le_succ n))⟩
          · exact ⟨hr z hz, (scheduledFrequencyHistory_all_bound V hV n r z hz).trans
              (hV (Nat.le_succ n))⟩
      rw [movingRootState_prime_support_iff value outside n _ _ _ _ XL XR (V (n + 1))
        hXL hXR hVL hVR hf]
      split_ifs <;> rfl
    · simp only [movingSupportedSampledWeight_zero_frequency value outside μ childBound
        pivotBound F _ hF n _ _ _ _ _ hr, star_zero, mul_zero, ite_self]
  · simp only [movingSupportedSampledWeight_zero_frequency value outside μ childBound
      pivotBound F _ hF n _ _ _ _ _ hl, mul_zero, zero_mul, ite_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeNodeFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual top node factor before summing descendant histories -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRootState_arithmetic_guard {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1)) (CL CR u : List σ)
    (XL XR P : ℕ) (s v w : ℤ) :
    ValidTransferNode (movingSlotSystem value childBound pivotBound)
      (movingRootState n t CL CR u XL XR) s v w P ↔
    movingNodeArithmeticGuard (childBound (n + 1)) (pivotBound (n + 1))
      (XL * MovingSlotReversal.naturalProduct value CL)
      (XR * MovingSlotReversal.naturalProduct value CR) s v w P := by
  constructor
  · intro h
    exact ⟨h.root_ne_zero, h.root_unit, h.relation, h.pivot_pos, h.pivot_bound,
      h.left_bound, h.right_bound, h.range_gap, h.pivot_unit⟩
  · rintro ⟨hs, hu, he, hp, hB, hv, hw, hgap, hunit⟩
    exact ⟨hs, hu, he, hp, hB, hv, hw, hgap, hunit⟩

/-- The original guarded summand is exactly a root-only factor times the
original two supported child coefficients. This is used only at actual prime
outer giants, where the extra cross-branch frequency tests follow from size. -/
theorem movingPrimeNodeFactor_term {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (hs : s ≠ 0) (hsV : s.natAbs ≤ V (n + 1))
    (l r : ScheduledFrequencyIndex V n)
    (small bulk : TreeLeafTuple (List σ) (n + 1))
    (a : TreeLeafTuple (Fin 4 → σ) n) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR) :
    let u := movingCompensationSlots n a
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let t := (s, scheduledFrequencyHistory V n l, scheduledFrequencyHistory V n r)
    let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
    let U := x.compensation value
    let v := frequencyRoot n t.2.1
    let w := frequencyRoot n t.2.2
    let p := reconstructedPivot
      (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)) (s * U)
    let L := movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n t.2.1
      (appendMovingSlotLeaves n u small.1) bulk.1 p XL
    let R := movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n t.2.2
      (appendMovingSlotLeaves n u small.2) bulk.2 p XR
    (if movingLocalSupport value outside x ∧
        (ValidTransferNode (movingSlotSystem value childBound pivotBound) x s v w (p * U) ∧
          0 < U) then (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) * L * star R else 0) =
      movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
        (flattenMovingSlots n u) XL XR s v w * L * star R := by
  intro u CL CR t x U v w p L R
  have h := movingRootState_prime_guard_product value outside μ childBound pivotBound V hV F hF
    φ G n s hs hsV l r small bulk a XL XR hXL hXR hVL hVR
    ((((U : ℝ) * φ (Real.log p - G (n + 1))) : ℝ) : ℂ)
    (ValidTransferNode (movingSlotSystem value childBound pivotBound) x s v w (p * U) ∧ 0 < U)
  calc
    _ = (if (XL :: XR :: ((CL ++ CR).map value ++ outside)).Pairwise Nat.Coprime ∧
        (ValidTransferNode (movingSlotSystem value childBound pivotBound) x s v w (p * U) ∧
          0 < U) then ((((U : ℝ) * φ (Real.log p - G (n + 1))) : ℝ) : ℂ) * L * star R
        else 0) := by
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | (split_ifs <;> rfl)
    _ = _ := by
      simp only [x, movingRootState_arithmetic_guard]
      unfold movingPrimeNodeFactor movingTopPivot
      dsimp only [x, U, p, v, w, t, movingRootState, MovingSlotState.compensation,
        MovingSlotState.leftProduct, MovingSlotState.rightProduct]
      simp only [ite_mul, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRootedSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact grouping of the two independent child frequency sums -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRootedFrequencyTree_root (V : ℕ → ℕ) (n : ℕ) (s : ℤ)
    (a : MovingDescendantFrequencyIndex V n) :
    frequencyRoot n (movingRootedFrequencyTree V n s a) = s := by
  cases n <;> rfl

theorem scheduledFrequencyIndex_sum_split (V : ℕ → ℕ) (n : ℕ)
    (f : ScheduledFrequencyIndex V n → ℂ) :
    (∑ a, f a) = ∑ s : transferFrequencyRange (V n),
      ∑ b : MovingDescendantFrequencyIndex V n,
        f ((scheduledFrequencyRootEquiv V n).symm (s, b)) := by
  simpa only [Fintype.sum_prod_type] using
    ((scheduledFrequencyRootEquiv V n).symm.sum_comp f).symm

theorem scheduledFrequencyHistory_from_root (V : ℕ → ℕ) (n : ℕ)
    (s : transferFrequencyRange (V n)) (a : MovingDescendantFrequencyIndex V n) :
    scheduledFrequencyHistory V n ((scheduledFrequencyRootEquiv V n).symm (s, a)) =
      movingRootedFrequencyTree V n s.val a := by
  rw [scheduledFrequencyRootEquiv_history, Equiv.apply_symm_apply]

/-- The two histories are independent after their roots are fixed. No number
of histories occurs in this exact distributive identity. The child functions
may depend on both roots through the reconstructed pivot. -/
theorem scheduledFrequency_bilinear_sum (V : ℕ → ℕ) (n : ℕ)
    (W : ℤ → ℤ → ℂ)
    (L R : ℤ → ℤ → FrequencyTree ℤ n → ℂ) :
    (∑ l : ScheduledFrequencyIndex V n, ∑ r : ScheduledFrequencyIndex V n,
      W (frequencyRoot n (scheduledFrequencyHistory V n l))
          (frequencyRoot n (scheduledFrequencyHistory V n r)) *
        L (frequencyRoot n (scheduledFrequencyHistory V n l))
          (frequencyRoot n (scheduledFrequencyHistory V n r)) (scheduledFrequencyHistory V n l) *
        star (R (frequencyRoot n (scheduledFrequencyHistory V n l))
          (frequencyRoot n (scheduledFrequencyHistory V n r)) (scheduledFrequencyHistory V n r))) =
      ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
        W v.val w.val *
          (∑ a : MovingDescendantFrequencyIndex V n,
            L v.val w.val (movingRootedFrequencyTree V n v.val a)) *
          star (∑ b : MovingDescendantFrequencyIndex V n,
            R v.val w.val (movingRootedFrequencyTree V n w.val b)) := by
  rw [scheduledFrequencyIndex_sum_split V n]
  simp_rw [scheduledFrequencyIndex_sum_split V n,
    scheduledFrequencyHistory_from_root, movingRootedFrequencyTree_root]
  simp only [star_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeCoefficientNode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete coefficient recursion at actual top primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFrequencyCoefficient_zero {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      n 0 small bulk XL XR = 0 := by
  unfold movingFrequencyCoefficient
  apply Finset.sum_eq_zero
  intro t _
  apply movingSupportedSampledWeight_zero_frequency value outside μ childBound pivotBound
    F _ hF n _ small bulk XL XR
  intro h
  apply h 0
  · cases n with
    | zero => exact List.mem_singleton_self _
    | succ n => exact List.mem_cons_self
  · rfl

/-- At actual prime giants, the original coefficient is the product recursion
in the two complete child coefficients. The shared compensation prior occurs
once, and every child retains its own descendant frequency and prime samples. -/
theorem movingFrequencyCoefficient_prime_node {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (hs : s ≠ 0) (hsV : s.natAbs ≤ V (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      (n + 1) s small bulk XL XR =
      ∑ a : TreeLeafTuple (Fin 4 → σ) n, (movingCompensationPrior (μ n) n a : ℂ) *
        ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
          let u := movingCompensationSlots n a
          let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
          let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
          let p := movingTopPivot value CL CR (flattenMovingSlots n u) XL XR s v.val w.val
          movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
              (flattenMovingSlots n u) XL XR s v.val w.val *
            movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n v.val
              (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
            star (movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n w.val
              (appendMovingSlotLeaves n u small.2) bulk.2 p XR) := by
  rw [movingFrequencyCoefficient_node]
  simp_rw [movingPrimeNodeFactor_term value outside μ childBound pivotBound V hV F hF
    φ G n s hs hsV _ _ small bulk _ XL XR hXL hXR hVL hVR]
  conv_lhs =>
    arg 2
    ext l
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [← Finset.mul_sum]
  let u := movingCompensationSlots n a
  let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
  let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
  let P := fun v w : ℤ => movingTopPivot value CL CR (flattenMovingSlots n u) XL XR s v w
  let W := fun v w : ℤ => movingPrimeNodeFactor value outside childBound pivotBound φ G n
    CL CR (flattenMovingSlots n u) XL XR s v w
  let L := fun v w t => movingSupportedSampledWeight value outside μ childBound pivotBound F
    (movingOriginalNode value childBound pivotBound φ G) n t
    (appendMovingSlotLeaves n u small.1) bulk.1 (P v w) XL
  let R := fun v w t => movingSupportedSampledWeight value outside μ childBound pivotBound F
    (movingOriginalNode value childBound pivotBound φ G) n t
    (appendMovingSlotLeaves n u small.2) bulk.2 (P v w) XR
  have h := scheduledFrequency_bilinear_sum V n W L R
  unfold movingFrequencyCoefficient
  apply congrArg (fun z : ℂ => (movingCompensationPrior (μ n) n a : ℂ) * z)
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCoefficientSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Current support inherited from the original summed coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFullSupport_local {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (h : movingFullSupport value outside T XL XR) :
    movingLocalSupport value outside ⟨n, T, XL, XR⟩ := by
  cases T with
  | leaf => exact h
  | node => exact ⟨h.1.1, h.2.1⟩

/-- A nonzero finite average contains a supported original sample. No
positivity, normalization, or conditioning of the prime prior is needed. -/
theorem movingSupportedSampledWeight_nonzero_support {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ)
    (h : movingSupportedSampledWeight value outside μ childBound pivotBound F E
      n t small bulk XL XR ≠ 0) :
    ∃ a : MovingSampleSlots σ n,
      movingFullSupport value outside (buildMovingSlotData n t small bulk a) XL XR := by
  rw [movingSupportedSampledWeight_eq, movingCompensatedAverage] at h
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have ht : movingSupportedSampleTerm value outside childBound pivotBound F E
      n t small bulk XL XR a ≠ 0 := by
    intro hz
    exact ha (by rw [hz, mul_zero])
  unfold movingSupportedSampleTerm movingSupportedWeight at ht
  refine ⟨a, ?_⟩
  by_contra hs
  exact ht (ite_eq_right hs)

/-- The root sum still has the actual current pairwise support and both
root-frequency units. These are the only support facts needed to attach the
original coefficient to the full Fourier transfer. -/
theorem movingFrequencyCoefficient_nonzero_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      n s small bulk XL XR ≠ 0) :
    (XL :: XR :: ((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value ++ outside)).Pairwise Nat.Coprime ∧
      IsCoprime (XL : ℤ) s ∧ IsCoprime (XR : ℤ) s := by
  rw [movingFrequencyCoefficient] at h
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨a, ha⟩ := movingSupportedSampledWeight_nonzero_support value outside μ childBound
    pivotBound F (movingOriginalNode value childBound pivotBound φ G) n
    (movingRootedFrequencyTree V n s t) small bulk XL XR ht
  let T := buildMovingSlotData n (movingRootedFrequencyTree V n s t) small bulk a
  have hlocal := movingFullSupport_local value outside T XL XR ha
  have hreg := buildMovingSlotData_regular_perm n (movingRootedFrequencyTree V n s t) small bulk a
  have hp : (T.currentSlots value XL XR ++ outside).Perm
      (XL :: XR :: ((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value ++ outside)) := by
    simpa only [MovingSlotData.currentSlots, List.cons_append] using
      (((hreg.map value).cons XR).cons XL).append_right outside
  have hpair := (hp.pairwise_iff (fun h => h.symm)).mp hlocal.1
  have hfreq : T.frequency = s := by
    rw [(buildMovingSlotData_follows n _ small bulk a).root, movingRootedFrequencyTree_root]
  have hL := ((T.frequencies_isCoprime (XL : ℤ)).mpr hlocal.2.1).root
  have hR := ((T.frequencies_isCoprime (XR : ℤ)).mpr hlocal.2.2.1).root
  exact ⟨hpair, hfreq ▸ hL, hfreq ▸ hR⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplatePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unchanged independent prime law under one template restoration -/

namespace Ostmann
open scoped Classical BigOperators

/-- This is literal finite Fubini; neither distinctness nor any history
support is conditioned into the prime law. -/
theorem movingReverseTemplate_average {A : Type*} [Fintype A] (n r m : ℕ)
    (ν : MovingRegularSlot n (4 + r) m → A → ℝ)
    (F : (MovingRegularSlot n (4 + r) m → A) → ℂ) :
    (∑ x, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x) =
      ∑ u : TreeLeafIndex n × Fin 4 → A,
        ((∏ i, ν (movingReverseTemplate n r m (.inl i)) (u i) : ℝ) : ℂ) *
        ∑ y : MovingRegularSlot n r m → A,
          ((∏ i, ν (movingReverseTemplate n r m (.inr i)) (y i) : ℝ) : ℂ) *
          F (movingRestoreSample n r m u y) := by
  have hr := finite_prior_reindex (movingReverseTemplate n r m) ν F
  simp only [finite_univ_canonical] at hr ⊢
  rw [← hr]
  let e := Equiv.sumArrowEquivProdArrow (TreeLeafIndex n × Fin 4) (MovingRegularSlot n r m) A
  have he := e.symm.sum_comp (fun x =>
    ((∏ i, ν (movingReverseTemplate n r m i) (x i) : ℝ) : ℂ) *
      F (x ∘ (movingReverseTemplate n r m).symm))
  simp only [finite_univ_canonical] at he ⊢
  rw [← he]
  have hs := Fintype.sum_prod_type (fun x :
      (TreeLeafIndex n × Fin 4 → A) × (MovingRegularSlot n r m → A) =>
    ((∏ i, ν (movingReverseTemplate n r m i) (e.symm x i) : ℝ) : ℂ) *
      F (e.symm x ∘ (movingReverseTemplate n r m).symm))
  simp only [finite_univ_canonical] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hp := Fintype.prod_sum_type (fun i :
      (TreeLeafIndex n × Fin 4) ⊕ MovingRegularSlot n r m =>
    ν (movingReverseTemplate n r m i) (e.symm (u, y) i))
  simp only [finite_univ_canonical] at hp
  rw [hp]
  simp only [e, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Complex.ofReal_mul]
  change _ * F (movingRestoreSample n r m u y) = _
  ring

theorem movingTemplateCompensationEquiv_prior {A : Type*}
    (μ : A → ℝ) (n : ℕ) (a : TreeLeafTuple (Fin 4 → A) n) :
    (∏ i, μ (movingTemplateCompensationEquiv A n a i)) = movingCompensationPrior μ n a := by
  rw [movingCompensationPrior_indexed, Fintype.prod_prod_type]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLeaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoring the four compensation primes in each actual leaf -/

namespace Ostmann
open scoped Classical BigOperators

theorem treeLeafTupleEquiv_append_slots {A : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List A) n) (j : TreeLeafIndex n) :
    treeLeafTupleEquiv (List A) n (appendMovingSlotLeaves n x y) j =
      treeLeafTupleEquiv (List A) n x j ++ treeLeafTupleEquiv (List A) n y j := by
  induction n with
  | zero => rfl
  | succ n ih => cases j with
    | inl j => exact ih x.1 y.1 j
    | inr j => exact ih x.2 y.2 j

theorem treeLeafTupleEquiv_compensation_slots {A : Type*} (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) (j : TreeLeafIndex n) :
    treeLeafTupleEquiv (List A) n (movingCompensationSlots n a) j =
      List.ofFn (treeLeafTupleEquiv (Fin 4 → A) n a j) := by
  induction n with
  | zero => rfl
  | succ n ih => cases j with
    | inl j => exact ih a.1 j
    | inr j => exact ih a.2 j

/-- Restoring the same compensation sample in every surviving leaf gives
exactly the small list required by the two child recursions. -/
theorem movingRestoreSample_small_leaves {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    treeLeafMap (List.map (movingRestoreSample n r m u y)) n (movingTemplateSmall n (4 + r) m) =
      appendMovingSlotLeaves n
        (movingCompensationSlots n ((treeLeafTupleEquiv (Fin 4 → A) n).symm
          (fun j i => u (j, i))))
        (treeLeafMap (List.map y) n (movingTemplateSmall n r m)) := by
  apply (treeLeafTupleEquiv (List A) n).injective
  funext j
  rw [treeLeafTupleEquiv_map, treeLeafTupleEquiv_append_slots,
    treeLeafTupleEquiv_compensation_slots, Equiv.apply_symm_apply,
    treeLeafTupleEquiv_map]
  simp only [movingTemplateSmall, bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn]
  rw [List.ofFn_add]
  change (List.ofFn (fun i : Fin 4 =>
      movingRestoreSample n r m u y (j, .inl (Fin.castAdd r i)))) ++
    (List.ofFn (fun i : Fin r =>
      movingRestoreSample n r m u y (j, .inl (Fin.natAdd 4 i)))) = _
  simp only [movingRestoreSample_small]
  rfl

theorem movingRestoreSample_bulk_leaves {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    treeLeafMap (List.map (movingRestoreSample n r m u y)) n
        (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m)) =
      treeLeafMap (List.map y) n (bulkSlotLeaves n m (movingTemplateBulk n r m)) := by
  rw [bulkSlotLeaves_map, bulkSlotLeaves_map]
  congr 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_NodeBulkProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder child products of the selected original prime leaves -/

namespace Ostmann
open scoped BigOperators

theorem treeLeafProduct_indexed {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafIndex n → G) :
    treeLeafProduct n ((treeLeafTupleEquiv G n).symm x) = ∏ i, x i := by
  induction n with
  | zero =>
    change Unit → G at x
    change x () = ∏ i : Unit, x i
    exact (Fintype.prod_subsingleton x ()).symm
  | succ n ih =>
    change (TreeLeafIndex n ⊕ TreeLeafIndex n) → G at x
    change treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inl i))) *
      treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inr i))) = _
    rw [ih, ih]
    change _ = ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n, x i
    exact (Fintype.prod_sum_type x).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact moduli of the regular-slot templates -/

namespace Ostmann
open scoped Classical BigOperators

theorem naturalProduct_bulkSlotLeaves {A : Type*} (value : A → ℕ) (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → A) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n (bulkSlotLeaves n m slot)) =
      ∏ i, value (slot i) := by
  rw [movingSlotValues_flatten]
  have h : movingSlotValues value n (bulkSlotLeaves n m slot) =
      (treeLeafTupleEquiv ℕ n).symm (fun j => ∏ i : Fin m, value (slot (j, i))) := by
    apply (treeLeafTupleEquiv ℕ n).injective
    funext j
    rw [movingSlotValues_indexed, Equiv.apply_symm_apply]
    simp only [bulkSlotLeaves, Equiv.apply_symm_apply, MovingSlotReversal.naturalProduct,
      List.map_ofFn, List.prod_ofFn]
    rfl
  rw [h, treeLeafProduct_indexed, Fintype.prod_prod_type]

/-- Every regular coordinate occurs once in the small/bulk leaf lists. -/
theorem movingTemplate_product {A : Type*} (value : A → ℕ) (n r m : ℕ)
    (y : MovingRegularSlot n r m → A) :
    MovingSlotReversal.naturalProduct (value ∘ y)
      (flattenMovingSlots n (movingTemplateSmall n r m) ++
        flattenMovingSlots n (bulkSlotLeaves n m (movingTemplateBulk n r m))) =
      ∏ i, value (y i) := by
  rw [movingNaturalProduct_append]
  unfold movingTemplateSmall
  rw [naturalProduct_bulkSlotLeaves, naturalProduct_bulkSlotLeaves]
  simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
    Function.comp_apply, movingTemplateBulk]
  rw [Finset.prod_mul_distrib]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplatePair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent surviving regular templates -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplatePairSample_small {A : Type*} (n r m : ℕ)
    (left right : MovingRegularSlot n r m → A) :
    treeLeafMap (List.map (movingTemplatePairSample n r m left right)) (n + 1)
      (movingTemplateSmall (n + 1) r m) =
      (treeLeafMap (List.map left) n (movingTemplateSmall n r m),
        treeLeafMap (List.map right) n (movingTemplateSmall n r m)) := by
  apply (treeLeafTupleEquiv (List A) (n + 1)).injective
  funext j
  rw [treeLeafTupleEquiv_map]
  cases j with
  | inl j =>
    change _ = treeLeafTupleEquiv (List A) n
      (treeLeafMap (List.map left) n (movingTemplateSmall n r m)) j
    rw [treeLeafTupleEquiv_map]
    simp only [movingTemplateSmall, bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn]
    rfl
  | inr j =>
    change _ = treeLeafTupleEquiv (List A) n
      (treeLeafMap (List.map right) n (movingTemplateSmall n r m)) j
    rw [treeLeafTupleEquiv_map]
    simp only [movingTemplateSmall, bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn]
    rfl

theorem movingTemplatePairSample_bulk {A : Type*} (n r m : ℕ)
    (left right : MovingRegularSlot n r m → A) :
    treeLeafMap (List.map (movingTemplatePairSample n r m left right)) (n + 1)
      (bulkSlotLeaves (n + 1) m (movingTemplateBulk (n + 1) r m)) =
      (treeLeafMap (List.map left) n (bulkSlotLeaves n m (movingTemplateBulk n r m)),
        treeLeafMap (List.map right) n (bulkSlotLeaves n m (movingTemplateBulk n r m))) := by
  apply (treeLeafTupleEquiv (List A) (n + 1)).injective
  funext j
  rw [treeLeafTupleEquiv_map]
  cases j with
  | inl j =>
    change _ = treeLeafTupleEquiv (List A) n
      (treeLeafMap (List.map left) n (bulkSlotLeaves n m (movingTemplateBulk n r m))) j
    rw [treeLeafTupleEquiv_map]
    simp only [bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn]
    rfl
  | inr j =>
    change _ = treeLeafTupleEquiv (List A) n
      (treeLeafMap (List.map right) n (bulkSlotLeaves n m (movingTemplateBulk n r m))) j
    rw [treeLeafTupleEquiv_map]
    simp only [bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn]
    rfl

private theorem finite_prior_sum_type {J K A : Type*}
    [Fintype J] [Fintype K] [Fintype A] (ν : J ⊕ K → A → ℝ)
    (F : (J ⊕ K → A) → ℂ) :
    (∑ x, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x) =
      ∑ l : J → A, ((∏ i, ν (.inl i) (l i) : ℝ) : ℂ) *
        ∑ r : K → A, ((∏ i, ν (.inr i) (r i) : ℝ) : ℂ) * F (Sum.elim l r) := by
  let e := Equiv.sumArrowEquivProdArrow J K A
  rw [← e.symm.sum_comp (fun x => ((∏ i, ν i (x i) : ℝ) : ℂ) * F x),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Fintype.prod_sum_type]
  simp only [e, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Complex.ofReal_mul]
  exact mul_assoc _ _ _

/-- Pairing surviving templates preserves the independent law. The shared
compensation law stays outside this identity. -/
theorem movingTemplatePair_average {A : Type*} [Fintype A] (n r m : ℕ)
    (ν : MovingRegularSlot (n + 1) r m → A → ℝ)
    (F : (MovingRegularSlot (n + 1) r m → A) → ℂ) :
    (∑ x, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x) =
      ∑ left : MovingRegularSlot n r m → A,
        ((∏ i, ν (.inl i.1, i.2) (left i) : ℝ) : ℂ) *
          ∑ right : MovingRegularSlot n r m → A,
            ((∏ i, ν (.inr i.1, i.2) (right i) : ℝ) : ℂ) *
              F (movingTemplatePairSample n r m left right) := by
  have hr := finite_prior_reindex (movingTemplatePairEquiv n r m) ν F
  simp only [finite_univ_canonical] at hr ⊢
  rw [← hr]
  have hs := finite_prior_sum_type (fun i => ν (movingTemplatePairEquiv n r m i))
    (fun x => F (x ∘ (movingTemplatePairEquiv n r m).symm))
  simp only [finite_univ_canonical] at hs
  exact hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original coefficient on the complete regular-slot template -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateCompensationEquiv_restore {σ : Type*} (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → σ) n) :
    (treeLeafTupleEquiv (Fin 4 → σ) n).symm
      (fun j i => movingTemplateCompensationEquiv σ n a (j, i)) = a := by
  change (treeLeafTupleEquiv (Fin 4 → σ) n).symm
    (treeLeafTupleEquiv (Fin 4 → σ) n a) = a
  exact Equiv.symm_apply_apply _ _

theorem movingTemplateCoefficient_restored {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (a : TreeLeafTuple (Fin 4 → σ) n) (y : MovingRegularSlot n r m → σ) (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m s
      (movingRestoreSample n r m (movingTemplateCompensationEquiv σ n a) y) XL XR =
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
      (appendMovingSlotLeaves n (movingCompensationSlots n a)
        (treeLeafMap (List.map y) n (movingTemplateSmall n r m)))
      (treeLeafMap (List.map y) n (bulkSlotLeaves n m (movingTemplateBulk n r m))) XL XR := by
  unfold movingTemplateCoefficient
  rw [movingRestoreSample_small_leaves, movingRestoreSample_bulk_leaves,
    movingTemplateCompensationEquiv_restore]

/-- Pair the surviving templates and restore each sampled compensation vector
in both children. This is the actual product recursion on the prescribed roles. -/
theorem movingTemplateCoefficient_prime_node {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (hs : s ≠ 0) (hsV : s.natAbs ≤ V (n + 1))
    (left right : MovingRegularSlot n r m → σ) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR) :
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s
      (movingTemplatePairSample n r m left right) XL XR =
    ∑ a : TreeLeafTuple (Fin 4 → σ) n, (movingCompensationPrior (μ n) n a : ℂ) *
      ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
        let CL := flattenMovingSlots n (treeLeafMap (List.map left) n (movingTemplateSmall n r m)) ++
          flattenMovingSlots n (treeLeafMap (List.map left) n (bulkSlotLeaves n m (movingTemplateBulk n r m)))
        let CR := flattenMovingSlots n (treeLeafMap (List.map right) n (movingTemplateSmall n r m)) ++
          flattenMovingSlots n (treeLeafMap (List.map right) n (bulkSlotLeaves n m (movingTemplateBulk n r m)))
        let u := flattenMovingSlots n (movingCompensationSlots n a)
        let p := movingTopPivot value CL CR u XL XR s v.val w.val
        movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR u XL XR s v.val w.val *
          movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m v.val
            (movingRestoreSample n r m (movingTemplateCompensationEquiv σ n a) left) p XL *
          star (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w.val
            (movingRestoreSample n r m (movingTemplateCompensationEquiv σ n a) right) p XR) := by
  rw [movingTemplateCoefficient, movingTemplatePairSample_small, movingTemplatePairSample_bulk]
  rw [movingFrequencyCoefficient_prime_node value outside μ childBound pivotBound V hV F hF
    φ G n s hs hsV _ _ XL XR hXL hXR hVL hVR]
  simp only [movingTemplateCoefficient_restored]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTransferSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the original pivot, compensation, and surviving slots -/

namespace Ostmann
open scoped Classical BigOperators

/-- The reindexing inserts precisely the same sampled compensation vector
which appears in the two child coefficients. -/
theorem movingTransferSlotEquiv_values {A : Type*} (value : A → ℕ) (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) (XL XR : ℕ) :
    (fun i => Sum.elim (fun b => if b then XL else XR)
      (value ∘ movingRestoreSample n r m u y) (movingTransferSlotEquiv n r m i)) =
    Sum.elim (Sum.elim (fun _ : Unit => XL) (value ∘ u))
      (Sum.elim (fun _ : Unit => XR) (value ∘ y)) := by
  funext i
  rcases i with ((j | j) | (j | j))
  · rfl
  · change value (movingRestoreSample n r m u y (movingReverseTemplate n r m (.inl j))) = value (u j)
    simp only [movingRestoreSample, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
  · rfl
  · change value (movingRestoreSample n r m u y (movingReverseTemplate n r m (.inr j))) = value (y j)
    simp only [movingRestoreSample, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTransferTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full Fourier transform in the actual transfer slot order -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTaggedTransform_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (giant : J → Bool)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform (p ∘ e) (giant ∘ e) greg ggiant favorable D s =
      movingTaggedTransform p giant greg ggiant favorable D s := by
  unfold movingTaggedTransform
  dsimp only [Function.comp_def]
  simp_rw [tupleCofactor_equiv e p hp]
  exact e.prod_comp (fun j => (if giant j then
      (fun t => if favorable (p j) then complexUnitPhase (ggiant (p j) t) else 0)
    else greg (p j))
      ((s : ZMod (p j)) * ((D * tupleCofactor p j : ℕ) : ZMod (p j))⁻¹))

/-- Restoring a compensation sample places precisely the extracted giant
and its compensation factors before the surviving giant and regular factors. -/
theorem movingTaggedTransform_restored {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (u : TreeLeafIndex n × Fin 4 → A)
    (y : MovingRegularSlot n r m → A) (XL XR : ℕ)
    (hXL : XL ≠ 0) (hXR : XR ≠ 0)
    (hu : ∀ i, value (u i) ≠ 0) (hy : ∀ i, value (y i) ≠ 0)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform
      (Sum.elim (fun b : Bool => if b then XL else XR)
        (value ∘ movingRestoreSample n r m u y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
    movingTaggedTransform
      (Sum.elim (Sum.elim (fun _ : Unit => XL) (value ∘ u))
        (Sum.elim (fun _ : Unit => XR) (value ∘ y)))
      (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
        (Sum.elim (fun _ : Unit => true) (fun _ => false))) greg ggiant favorable D s := by
  let p : Bool ⊕ MovingRegularSlot n (4 + r) m → ℕ :=
    Sum.elim (fun b : Bool => if b then XL else XR)
    (value ∘ movingRestoreSample n r m u y)
  let t : Bool ⊕ MovingRegularSlot n (4 + r) m → Bool :=
    Sum.elim (fun _ => true) (fun _ => false)
  have hp : ∀ i, p i ≠ 0 := by
    intro i
    rcases i with (b | i)
    · cases b <;> assumption
    · change value (movingRestoreSample n r m u y i) ≠ 0
      unfold movingRestoreSample
      dsimp only [Function.comp_apply]
      cases he : (movingReverseTemplate n r m).symm i with
      | inl j => exact hu j
      | inr j => exact hy j
  have ht : t ∘ movingTransferSlotEquiv n r m =
      Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
        (Sum.elim (fun _ : Unit => true) (fun _ => false)) := by
    funext i
    rcases i with ((i | i) | (i | i)) <;> rfl
  have he := movingTaggedTransform_equiv (movingTransferSlotEquiv n r m) p hp t
    greg ggiant favorable D s
  rw [ht] at he
  have hv := movingTransferSlotEquiv_values value n r m u y XL XR
  change p ∘ movingTransferSlotEquiv n r m = _ at hv
  rw [hv] at he
  exact he.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPairedTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving Fourier factors in the paired regular template -/

namespace Ostmann
open scoped Classical BigOperators

/-- Both surviving giants and every regular factor occur once in the next
full transform. This is independent of the reconstructed pivot. -/
theorem movingTaggedTransform_paired {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (left right : MovingRegularSlot n r m → A) (XL XR : ℕ)
    (hXL : XL ≠ 0) (hXR : XR ≠ 0)
    (hleft : ∀ i, value (left i) ≠ 0) (hright : ∀ i, value (right i) ≠ 0)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform
      (Sum.elim (Sum.elim (fun _ : Unit => XL) (value ∘ left))
        (Sum.elim (fun _ : Unit => XR) (value ∘ right)))
      (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
        (Sum.elim (fun _ : Unit => true) (fun _ => false))) greg ggiant favorable D s =
    movingTaggedTransform
      (Sum.elim (fun b : Bool => if b then XL else XR)
        (value ∘ movingTemplatePairSample n r m left right))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s := by
  let p : Bool ⊕ MovingRegularSlot (n + 1) r m → ℕ :=
    Sum.elim (fun b => if b then XL else XR)
      (value ∘ movingTemplatePairSample n r m left right)
  let t : Bool ⊕ MovingRegularSlot (n + 1) r m → Bool :=
    Sum.elim (fun _ => true) (fun _ => false)
  have hp : ∀ i, p i ≠ 0 := by
    intro i
    rcases i with (b | ⟨j, k⟩)
    · cases b <;> assumption
    · cases j with
      | inl j => exact hleft (j, k)
      | inr j => exact hright (j, k)
  have ht : t ∘ movingPairedGiantEquiv n r m =
      Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
        (Sum.elim (fun _ : Unit => true) (fun _ => false)) := by
    funext i
    rcases i with ((i | i) | (i | i)) <;> rfl
  have hv : p ∘ movingPairedGiantEquiv n r m =
      Sum.elim (Sum.elim (fun _ : Unit => XL) (value ∘ left))
        (Sum.elim (fun _ : Unit => XR) (value ∘ right)) := by
    funext i
    rcases i with ((i | i) | (i | i)) <;> rfl
  have he := movingTaggedTransform_equiv (movingPairedGiantEquiv n r m) p hp t
    greg ggiant favorable D s
  rw [ht, hv] at he
  exact he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single family of normalized transforms for varying sampled primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem normalizedResidueFamily_eq (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) [NeZero q] :
    normalizedResidueFamily sets q = normalizedResidueTransform (sets q) := by
  simp only [normalizedResidueFamily, dite_eq_right (NeZero.ne q)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOneGiant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One surviving giant and its actual regular Fourier factors -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingOneGiantModuli_product {I : Type*} [Fintype I] (X : ℕ) (p : I → ℕ) :
    (∏ i, movingOneGiantModuli X p i) = X * ∏ i, p i := by
  simp only [movingOneGiantModuli, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.prod_unique]

theorem movingOneGiantFactors_neg {I : Type*} (X : ℕ) (p : I → ℕ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ x, ggiant X (-x) = conj (ggiant X x))
    (hregular : ∀ i x, greg (p i) (-x) = conj (greg (p i) x))
    (i : Unit ⊕ I) (x : ZMod (movingOneGiantModuli X p i)) :
    movingOneGiantFactors X p greg ggiant favorable i (-x) =
      conj (movingOneGiantFactors X p greg ggiant favorable i x) := by
  cases i with
  | inl _ =>
    dsimp only [movingOneGiantFactors]
    split_ifs
    · exact (congrArg complexUnitPhase (hgiant x)).trans (complexUnitPhase_conj _)
    · exact (map_zero _).symm
  | inr i => exact hregular i x

attribute [local instance] OAI.Ostmann.oneGiantSum_neZero
/-- The restored full factor is in the order required by giant transfer. -/
theorem movingOneGiant_restored {σ : Type*} (value : σ → ℕ)
    (n r m : ℕ) (u : TreeLeafIndex n × Fin 4 → σ)
    (y : MovingRegularSlot n r m → σ) (P X : ℕ)
    (hP : P ≠ 0) (hX : X ≠ 0) (hu : ∀ i, value (u i) ≠ 0) (hy : ∀ i, value (y i) ≠ 0)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    let _ : NeZero P := ⟨hP⟩
    let _ : NeZero X := ⟨hX⟩
    let _ : ∀ i, NeZero ((value ∘ u) i) := fun i => ⟨hu i⟩
    let _ : ∀ i, NeZero ((value ∘ y) i) := fun i => ⟨hy i⟩
    movingTaggedTransform
      (Sum.elim (fun b : Bool => if b then P else X)
        (value ∘ movingRestoreSample n r m u y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
    movingRegularTransform
      (Sum.elim (movingOneGiantModuli P (value ∘ u)) (movingOneGiantModuli X (value ∘ y)))
      (movingSumFactors (movingOneGiantModuli P (value ∘ u))
        (movingOneGiantModuli X (value ∘ y))
        (movingOneGiantFactors P (value ∘ u) greg ggiant favorable)
        (movingOneGiantFactors X (value ∘ y) greg ggiant favorable)) D s := by
  dsimp only
  rw [movingTaggedTransform_restored value n r m u y P X hP hX hu hy]
  unfold movingTaggedTransform movingRegularTransform
  apply Finset.prod_congr rfl
  intro i _
  rcases i with ((i | i) | (i | i)) <;> rfl

/-- The original compensation, giant, and surviving priors may be left
abstract while reindexing their common full Fourier factor. -/
theorem movingOneGiant_restored_average {σ A : Type} [Fintype σ] [Fintype A]
    (value : σ → ℕ) (hvalue : ∀ z, value z ≠ 0) (n r m : ℕ)
    (P : Finset ℕ) (hP : ∀ p : P, (p : ℕ) ≠ 0)
    (X : A → ℕ) (hX : ∀ a, X a ≠ 0) (y : A → MovingRegularSlot n r m → σ)
    (v : A → ℤ) (D : ℕ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (wU : (TreeLeafIndex n × Fin 4 → σ) → ℂ) (wP : P → ℂ)
    (W : (TreeLeafIndex n × Fin 4 → σ) → P → A → ℂ) :
    let _ : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨hP p⟩
    let _ : ∀ a, NeZero (X a) := fun a => ⟨hX a⟩
    let _ : ∀ z, NeZero (value z) := fun z => ⟨hvalue z⟩
    let _ : ∀ (u : TreeLeafIndex n × Fin 4 → σ) i, NeZero ((value ∘ u) i) := fun u i => ⟨hvalue (u i)⟩
    let _ : ∀ a i, NeZero ((value ∘ y a) i) := fun a i => ⟨hvalue (y a i)⟩
    (∑ u : TreeLeafIndex n × Fin 4 → σ, wU u * ∑ p : P, wP p * ∑ a, W u p a *
      movingTaggedTransform
        (Sum.elim (fun b : Bool => if b then (p : ℕ) else X a)
          (value ∘ movingRestoreSample n r m u (y a)))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D (v a)) =
    ∑ u : TreeLeafIndex n × Fin 4 → σ, wU u * ∑ p : P, wP p * ∑ a, W u p a *
      movingRegularTransform
        (Sum.elim (movingOneGiantModuli (p : ℕ) (value ∘ u))
          (movingOneGiantModuli (X a) (value ∘ y a)))
        (movingSumFactors (movingOneGiantModuli (p : ℕ) (value ∘ u))
          (movingOneGiantModuli (X a) (value ∘ y a))
          (movingOneGiantFactors (p : ℕ) (value ∘ u) greg ggiant favorable)
          (movingOneGiantFactors (X a) (value ∘ y a) greg ggiant favorable)) D (v a) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro u _
  apply congrArg (fun z : ℂ => wU u * z)
  apply Finset.sum_congr rfl
  intro p _
  apply congrArg (fun z : ℂ => wP p * z)
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun z : ℂ => W u p a * z)
    (movingOneGiant_restored value n r m u (y a) p (X a) (hP p) (hX a)
      (fun i => hvalue (u i)) (fun i => hvalue (y a i)) greg ggiant favorable D (v a))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingChildListSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The restored child lists supply the support used by the transfer -/

namespace Ostmann
open scoped Classical BigOperators

/-- Restoring compensation does not change its order-free current support. -/
theorem movingFrequencyCoefficient_child_pairwise {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (u small bulk : TreeLeafTuple (List σ) n) (p X : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
      (appendMovingSlotLeaves n u small) bulk p X ≠ 0) :
    (p :: X :: ((flattenMovingSlots n u).map value ++
      ((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value ++ outside))).Pairwise Nat.Coprime := by
  have hs := (movingFrequencyCoefficient_nonzero_support value outside μ childBound
    pivotBound V F φ G n s (appendMovingSlotLeaves n u small) bulk p X h).1
  have hp := (flattenMovingSlots_append_perm n u small).append_right (flattenMovingSlots n bulk)
  have hp' := (((hp.map value).append_right outside).cons X).cons p
  apply (hp'.pairwise_iff (fun h => h.symm)).mp at hs
  simpa only [List.map_append, List.append_assoc] using hs

/-- A restored child is disjoint from the inserted giant and its shared
compensation vector. These are precisely the product units needed in the
integer substitution. -/
theorem restored_child_product_support (u small outside : List ℕ) (p X : ℕ)
    (h : (p :: X :: (u ++ (small ++ outside))).Pairwise Nat.Coprime) :
    (X :: (small ++ outside)).Pairwise Nat.Coprime ∧
      (X * small.prod).Coprime (p * u.prod) := by
  obtain ⟨hp, htail⟩ := List.pairwise_cons.mp h
  obtain ⟨hX, hrest⟩ := List.pairwise_cons.mp htail
  obtain ⟨_, hsmall, hcross⟩ := List.pairwise_append.mp hrest
  refine ⟨List.pairwise_cons.mpr ⟨?_, hsmall⟩, ?_⟩
  · exact fun a ha => hX a (List.mem_append_right u ha)
  · apply Nat.Coprime.mul_right
    · apply Nat.Coprime.mul_left
      · exact (hp X List.mem_cons_self).symm
      · apply Nat.coprime_list_prod_left_iff.mpr
        intro a ha
        exact (hp a (List.mem_cons_of_mem X
          (List.mem_append_right u (List.mem_append_left outside ha)))).symm
    · apply Nat.coprime_list_prod_right_iff.mpr
      intro a ha
      apply Nat.Coprime.mul_left
      · exact hX a (List.mem_append_left (small ++ outside) ha)
      · apply Nat.coprime_list_prod_left_iff.mpr
        intro b hb
        exact (hcross a ha b (List.mem_append_left outside hb)).symm

/-- The inherited product in a nonzero child is coprime to the composite
pivot, even when the newly inserted giant is only an integer. -/
theorem movingFrequencyCoefficient_child_products {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (u small bulk : TreeLeafTuple (List σ) n) (p X : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
      (appendMovingSlotLeaves n u small) bulk p X ≠ 0) :
    (X :: (((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value) ++ outside)).Pairwise Nat.Coprime ∧
      (X * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n small ++ flattenMovingSlots n bulk)).Coprime
        (p * MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)) := by
  exact restored_child_product_support _ _ _ p X
    (movingFrequencyCoefficient_child_pairwise value outside μ childBound pivotBound V F φ G
      n s u small bulk p X h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeNodeTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic guard is automatic in the genuine off-diagonal -/

namespace Ostmann
open scoped Classical BigOperators

/-- On a retained integer substitution, the supported child coefficients
supply the pairwise and frequency-unit tests of the new node. Its remaining
bounds are exactly the range inequalities used by the full transfer theorem. -/
theorem movingPrimeNodeFactor_transfer_product {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (u : TreeLeafTuple (List σ) n) (small bulk : TreeLeafTuple (List σ) (n + 1))
    (XL XR : ℕ) (s v w : ℤ) (I : Finset ℕ)
    (hI : ∀ p ∈ I, 0 < p)
    (hsV : s.natAbs ≤ V (n + 1))
    (hv : v.natAbs ≤ childBound (n + 1)) (hw : w.natAbs ≤ childBound (n + 1)) :
    let U := MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let LH := XL * MovingSlotReversal.naturalProduct value CL
    let RH := XR * MovingSlotReversal.naturalProduct value CR
    let p := movingTopPivot value CL CR (flattenMovingSlots n u) XL XR s v w
    let A := movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n v
      (appendMovingSlotLeaves n u small.1) bulk.1 p XL
    let B := movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n w
      (appendMovingSlotLeaves n u small.2) bulk.2 p XR
    validTransferredPivot I (v * RH - w * LH) (s * U) →
    (∀ p ∈ I, p * U ≤ pivotBound (n + 1)) →
    2 * pivotBound (n + 1) * childBound (n + 1) < RH →
    (∀ q, q.Prime → q ∣ RH → V (n + 1) < q) →
    (∀ q, q.Prime → q ∣ U → childBound (n + 1) < q) →
    movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
      (flattenMovingSlots n u) XL XR s v w * A * star B =
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) * A * star B := by
  intro U CL CR LH RH p A B htrans hbound hgap hRH hU
  by_cases hA : A = 0
  · simp only [hA, mul_zero, zero_mul]
  by_cases hB : B = 0
  · simp only [hB, star_zero, mul_zero]
  have hs : s ≠ 0 := left_ne_zero_of_mul htrans.1
  have hUpos : 0 < U := Nat.pos_of_ne_zero (fun hz => htrans.1 (by simp [hz]))
  have hpI : p ∈ I := htrans.2.2.2
  have hrel : v * (RH : ℤ) - w * (LH : ℤ) = s * (p * U : ℕ) := by
    have he := validTransferredPivot_equation I (v * RH - w * LH) (s * U) htrans
    change v * (RH : ℤ) - w * (LH : ℤ) = (s * U) * p at he
    calc
      _ = (s * U) * p := he
      _ = _ := by rw [Nat.cast_mul]; ring
  have hleft := movingFrequencyCoefficient_child_products value outside μ childBound pivotBound V
    F φ G n v u small.1 bulk.1 p XL hA
  have hright := movingFrequencyCoefficient_child_products value outside μ childBound pivotBound V
    F φ G n w u small.2 bulk.2 p XR hB
  have hLunit : LH.Coprime (p * U) := hleft.2
  have hcop : LH.Coprime RH := transferred_products_coprime LH RH v w s (p * U) hs hrel
    (fun q hq _ hd => hsV.trans_lt (hRH q hq hd))
    (common_prime_pivot_unit (p * U) LH RH hLunit)
  have hmerged := pairwise_coprime_merge_shared (XL :: CL.map value) (XR :: CR.map value)
    outside hleft.1 hright.1 (by simpa only [LH, RH, List.prod_cons, MovingSlotReversal.naturalProduct] using hcop)
  have hperm : ((XL :: CL.map value) ++ (XR :: CR.map value) ++ outside).Perm
      (XL :: XR :: ((CL ++ CR).map value ++ outside)) := by
    apply List.perm_iff_count.mpr
    intro a
    simp only [List.count_cons, List.count_append, List.map_append]
    omega
  have hpair := (hperm.pairwise_iff (fun h => h.symm)).mp hmerged
  have hw0 : w ≠ 0 := by
    intro hz
    apply hB
    subst w
    exact movingFrequencyCoefficient_zero value outside μ childBound pivotBound V F hF φ G
      n (appendMovingSlotLeaves n u small.2) bulk.2 p XR
  have hpw := (movingFrequencyCoefficient_nonzero_support value outside μ childBound pivotBound V
    F φ G n w (appendMovingSlotLeaves n u small.2) bulk.2 p XR hB).2.1
  have hpw' : p.Coprime w.natAbs := by
    simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using hpw
  have hUw : U.Coprime w.natAbs := large_prime_factors_coprime_frequency U w hw0
    (fun q hq hd => hw.trans_lt (hU q hq hd))
  have hroot : IsCoprime s (RH : ℤ) := by
    have h := large_prime_factors_coprime_frequency RH s hs
      (fun q hq hd => hsV.trans_lt (hRH q hq hd))
    simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using h.symm
  have hguard : movingNodeArithmeticGuard (childBound (n + 1)) (pivotBound (n + 1))
      LH RH s v w (p * U) :=
    ⟨hs, hroot, hrel, Nat.mul_pos (hI p hpI) hUpos, hbound p hpI, hv, hw, hgap,
      hpw'.mul_left hUw⟩
  have hfactor : movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
      (flattenMovingSlots n u) XL XR s v w =
      (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) := by
    unfold movingPrimeNodeFactor
    exact ite_eq_left ⟨hpair, hguard, hUpos⟩
  rw [hfactor]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeNodeSubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact identification of the coefficient node with integer substitution -/

namespace Ostmann
open scoped Classical BigOperators

/-- Every nonzero original node factor comes from the unique positive integer
substitution in its cutoff range. -/
theorem movingPrimeNodeFactor_valid {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (CL CR u : List σ)
    (XL XR : ℕ) (s v w : ℤ) (I : Finset ℕ)
    (hI : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hf : movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR u XL XR s v w ≠ 0) :
    validTransferredPivot I
      (v * (XR * MovingSlotReversal.naturalProduct value CR : ℕ) -
        w * (XL * MovingSlotReversal.naturalProduct value CL : ℕ))
      (s * MovingSlotReversal.naturalProduct value u) := by
  let U := MovingSlotReversal.naturalProduct value u
  let p := movingTopPivot value CL CR u XL XR s v w
  unfold movingPrimeNodeFactor at hf
  dsimp only at hf
  split_ifs at hf with hguard
  · rcases hguard with ⟨_, hnode, hU⟩
    rcases hnode with ⟨hs, _, hrel, hpU, _, _, _, _, _⟩
    change (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) ≠ 0 at hf
    have hp : 0 < p := Nat.pos_of_mul_pos_right hpU
    have hφ : φ (Real.log p - G (n + 1)) ≠ 0 := by
      intro hz
      exact hf (by simp only [hz, mul_zero, Complex.ofReal_zero])
    apply validTransferredPivot_of_eq I _ _ (mul_ne_zero hs (by exact_mod_cast hU.ne'))
      p hp (hI p hp hφ)
    change _ = (s * (U : ℤ)) * (p : ℤ)
    calc
      _ = s * (p * U : ℕ) := hrel
      _ = _ := by rw [Nat.cast_mul]; ring
  · exact (hf rfl).elim

/-- The new coefficient term is exactly the off-diagonal integer-substitution
term from the full transform transfer, with its original two child factors. -/
theorem movingPrimeNodeFactor_substitution {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (u : TreeLeafTuple (List σ) n) (small bulk : TreeLeafTuple (List σ) (n + 1))
    (XL XR : ℕ) (s v w : ℤ) (I : Finset ℕ)
    (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hsV : s.natAbs ≤ V (n + 1))
    (hv : v.natAbs ≤ childBound (n + 1)) (hw : w.natAbs ≤ childBound (n + 1)) :
    let U := MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let LH := XL * MovingSlotReversal.naturalProduct value CL
    let RH := XR * MovingSlotReversal.naturalProduct value CR
    let p := movingTopPivot value CL CR (flattenMovingSlots n u) XL XR s v w
    let A := movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n v
      (appendMovingSlotLeaves n u small.1) bulk.1 p XL
    let B := movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n w
      (appendMovingSlotLeaves n u small.2) bulk.2 p XR
    (∀ p ∈ I, p * U ≤ pivotBound (n + 1)) →
    2 * pivotBound (n + 1) * childBound (n + 1) < RH →
    (∀ q, q.Prime → q ∣ RH → V (n + 1) < q) →
    (∀ q, q.Prime → q ∣ U → childBound (n + 1) < q) →
    movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
      (flattenMovingSlots n u) XL XR s v w * A * star B =
      if validTransferredPivot I (v * RH - w * LH) (s * U) then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) * A * star B else 0 := by
  intro U CL CR LH RH p A B hbound hgap hRH hU
  by_cases h : validTransferredPivot I (v * RH - w * LH) (s * U)
  · rw [ite_eq_left h]
    exact movingPrimeNodeFactor_transfer_product value outside μ childBound pivotBound V F hF φ G n
      u small bulk XL XR s v w I hI hsV hv hw h hbound hgap hRH hU
  · rw [ite_eq_right h]
    have hz : movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
        (flattenMovingSlots n u) XL XR s v w = 0 := by
      by_contra hf
      exact h (movingPrimeNodeFactor_valid value outside childBound pivotBound φ G n CL CR
        (flattenMovingSlots n u) XL XR s v w I hφ hf)
    rw [hz, zero_mul, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateIntegerNode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integer node on the original independent template law -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateMapped_product {σ : Type*} (value : σ → ℕ) (n r m : ℕ)
    (y : MovingRegularSlot n r m → σ) :
    MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n (treeLeafMap (List.map y) n (movingTemplateSmall n r m)) ++
        flattenMovingSlots n (treeLeafMap (List.map y) n
          (bulkSlotLeaves n m (movingTemplateBulk n r m)))) = ∏ i, value (y i) := by
  simpa only [flattenMovingSlots_map, MovingSlotReversal.naturalProduct,
    List.map_append, List.map_map, Function.comp_def] using movingTemplate_product value n r m y

theorem movingTemplateCompensationEquiv_product {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → σ) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n (movingCompensationSlots n a)) =
      ∏ i, value (movingTemplateCompensationEquiv σ n a i) := by
  rw [movingCompensationProduct_indexed, Fintype.prod_prod_type]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateAmplitudeRestore
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoring the original independent compensation law in the amplitude -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original current amplitude is the giant-transfer expression with
one shared compensation draw outside its two giant and frequency sums. -/
theorem movingTemplatePrimeAmplitude_restore {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
      Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable =
    ∑ u : TreeLeafIndex n × Fin 4 → σ, ((∏ i, μ n (u i) : ℝ) : ℂ) *
      ∑ XL : Pg, (ρ XL : ℂ) * ∑ XR : Pg, (ρ XR : ℂ) *
        ∑ s : transferFrequencyRange (V n),
          ∑ y : MovingRegularSlot n r m → σ, ((∏ i, ν i (y i) : ℝ) : ℂ) *
            (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m
              s.val (movingRestoreSample n r m u y) XL XR *
              movingTaggedTransform
                (Sum.elim (fun b : Bool => if b then (XL : ℕ) else (XR : ℕ))
                  (value ∘ movingRestoreSample n r m u y))
                (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val) := by
  unfold movingTemplatePrimeAmplitude
  have hinner (XL XR : Pg) (s : transferFrequencyRange (V n)) :=
    movingReverseTemplate_average n r m (movingTemplateRestoredPrior n r m (μ n) ν)
      (fun y => movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
        n (4 + r) m s.val y XL XR *
        movingTaggedTransform
          (Sum.elim (fun b : Bool => if b then (XL : ℕ) else (XR : ℕ)) (value ∘ y))
          (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val)
  simp_rw [hinner]
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext XL
    arg 2
    ext XR
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext XL
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro XL _
  apply Finset.sum_congr rfl
  intro XR _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  simp only [movingTemplateRestoredPrior, Equiv.symm_apply_apply, Sum.elim_inl,
    Sum.elim_inr]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateTransferSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer support derived from nonzero original template coefficients -/

namespace Ostmann
open scoped Classical BigOperators

private theorem indexed_coprime_of_list {I : Type*} (p : I → ℕ) (L : List I)
    (hcover : ∀ i, i ∈ L) (h : (L.map p).Pairwise Nat.Coprime) :
    Pairwise (fun i j => (p i).Coprime (p j)) := by
  have h' : L.Pairwise (fun i j => i ≠ j → (p i).Coprime (p j)) :=
    (List.pairwise_map.mp h).imp (fun {i j} hij (_ : i ≠ j) => hij)
  have hflip : L.Pairwise (flip (fun i j => i ≠ j → (p i).Coprime (p j))) :=
    h'.imp (fun {i j} hij (hji : j ≠ i) => (hij hji.symm).symm)
  intro i j hij
  exact h'.forall_of_forall_of_flip (fun a _ haa => (haa rfl).elim) hflip
    (hcover i) (hcover j) hij

/-- The complete current Fourier slots inherit pairwise and outside
coprimality directly from the support of their coefficient. -/
theorem movingTemplateCoefficient_transfer_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (q : Bool → ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n r m s y (q true) (q false) ≠ 0) :
    Pairwise (fun i j => (Sum.elim q (value ∘ y) i).Coprime (Sum.elim q (value ∘ y) j)) ∧
      ∀ i, outside.prod.Coprime (Sum.elim q (value ∘ y) i) := by
  let L : List (Bool ⊕ MovingRegularSlot n r m) :=
    [.inl true, .inl false] ++ (movingTemplateSlotList n r m).map Sum.inr
  let p := Sum.elim q (value ∘ y)
  have hcover : ∀ i, i ∈ L := by
    intro i
    cases i with
    | inl b => cases b <;> simp [L]
    | inr i => exact List.mem_append_right _ (List.mem_map.mpr
        ⟨i, mem_movingTemplateSlotList n r m i, rfl⟩)
  have hs := (movingFrequencyCoefficient_nonzero_support value outside μ childBound
    pivotBound V F φ G n s _ _ (q true) (q false) h).1
  have hs' : (L.map p ++ outside).Pairwise Nat.Coprime := by
    simpa only [L, p, List.map_append, List.map_cons, List.map_nil, List.map_map,
      List.cons_append, List.nil_append, Sum.elim_inl, Sum.elim_inr,
      movingTemplateSlotList, flattenMovingSlots_map, Function.comp_def] using hs
  obtain ⟨hp, _, ho⟩ := List.pairwise_append.mp hs'
  refine ⟨indexed_coprime_of_list p L hcover hp, ?_⟩
  intro i
  apply Nat.coprime_list_prod_left_iff.mpr
  intro d hd
  exact (ho (p i) (List.mem_map.mpr ⟨i, hcover i, rfl⟩) d hd).symm

/-- Restrict the full support to the two pieces of a restored child.
This supplies the exact support fields of the giant transfer. -/
theorem movingTemplateCoefficient_restored_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → σ) (y : MovingRegularSlot n r m → σ)
    (p X : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n (4 + r) m s (movingRestoreSample n r m u y) p X ≠ 0) :
    let Q := Sum.elim (fun _ : Unit => p) (value ∘ u)
    let L := Sum.elim (fun _ : Unit => X) (value ∘ y)
    Pairwise (fun i j => (Q i).Coprime (Q j)) ∧
      (∀ i, outside.prod.Coprime (Q i)) ∧
      Pairwise (fun i j => (L i).Coprime (L j)) ∧
      (∏ i, L i).Coprime (∏ i, Q i) ∧
      (∀ i, outside.prod.Coprime (L i)) := by
  let q : Bool → ℕ := fun b => if b then p else X
  have hs := movingTemplateCoefficient_transfer_support value outside μ childBound pivotBound V
    F φ G n (4 + r) m s (movingRestoreSample n r m u y) q h
  have he := movingTransferSlotEquiv_values value n r m u y p X
  let f := Sum.elim (Sum.elim (fun _ : Unit => p) (value ∘ u))
    (Sum.elim (fun _ : Unit => X) (value ∘ y))
  have hp : Pairwise (fun i j => (f i).Coprime (f j)) := by
    intro i j hij
    have hx := hs.1 ((movingTransferSlotEquiv n r m).injective.ne hij)
    change (Sum.elim q (value ∘ movingRestoreSample n r m u y)
      (movingTransferSlotEquiv n r m i)).Coprime
      (Sum.elim q (value ∘ movingRestoreSample n r m u y)
      (movingTransferSlotEquiv n r m j)) at hx
    rw [congrFun he i, congrFun he j] at hx
    exact hx
  have hd : ∀ i, outside.prod.Coprime (f i) := by
    intro i
    have hx := hs.2 (movingTransferSlotEquiv n r m i)
    rw [congrFun he i] at hx
    exact hx
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hp (fun he => hij (Sum.inl.inj he))
  · intro i
    exact hd (.inl i)
  · intro i j hij
    exact hp (fun he => hij (Sum.inr.inj he))
  · apply Nat.coprime_prod_left_iff.mpr
    intro i _
    apply Nat.coprime_prod_right_iff.mpr
    intro j _
    exact hp (Sum.inr_ne_inl)
  · intro i
    exact hd (.inr i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateWeightedSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original external weight multiplying a restored coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateTransferWeight_support {σ A : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (v : A → ℤ) (α : A → ℂ) (X : A → ℕ)
    (y : A → MovingRegularSlot n r m → σ)
    (u : TreeLeafIndex n × Fin 4 → σ) (p : ℕ) (a : A)
    (h : movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m
      v α X y u p a ≠ 0) :
    let Q := Sum.elim (fun _ : Unit => p) (value ∘ u)
    let L := Sum.elim (fun _ : Unit => X a) (value ∘ y a)
    Pairwise (fun i j => (Q i).Coprime (Q j)) ∧
      (∀ i, outside.prod.Coprime (Q i)) ∧
      Pairwise (fun i j => (L i).Coprime (L j)) ∧
      (∏ i, L i).Coprime (∏ i, Q i) ∧
      (∀ i, outside.prod.Coprime (L i)) :=
  movingTemplateCoefficient_restored_support value outside μ childBound pivotBound V F φ G
    n r m (v a) u (y a) p (X a) (right_ne_zero_of_mul h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving giant, regular tuple and frequency as one transfer index -/

namespace Ostmann
open scoped Classical BigOperators

/-- The frequency is part of the transfer index and has counting measure.
Only the giant and regular prime coordinates carry probability weights. -/
theorem movingTemplatePrimeAmplitude_index {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
      Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable =
    ∑ u : TreeLeafIndex n × Fin 4 → σ, ((∏ i, μ n (u i) : ℝ) : ℂ) *
      ∑ p : Pg, (ρ p : ℂ) * ∑ a : MovingAmplitudeIndex σ Pg n r m V,
        movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m
          (fun a => a.2.2.val) (fun a => (movingAmplitudePrior Pg n r m V ρ ν a : ℂ))
          (fun a => (a.1 : ℕ)) (fun a => a.2.1) u p a *
          movingTaggedTransform
            (Sum.elim (fun b : Bool => if b then (p : ℕ) else (a.1 : ℕ))
              (value ∘ movingRestoreSample n r m u a.2.1))
            (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod a.2.2.val := by
  rw [movingTemplatePrimeAmplitude_restore]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  simp only [MovingAmplitudeIndex, Fintype.sum_prod_type, movingTemplateTransferWeight,
    movingAmplitudePrior, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeRowNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact CRT row norm used by the giant-only transfer -/

namespace Ostmann
open scoped Classical BigOperators

/-- Both the giant's bounded row and the exact compensation-prime energies
enter multiplicatively, at their actual modulus sizes. -/
theorem moving_crt_row_energy {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, NeZero (p j)] [NeZero (∏ j, p j)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (g : ∀ j, ZMod (p j) → ℂ)
    (henergy : ∀ j, (∑ x, ‖g j x‖ ^ 2) ≤ (p j : ℝ)) :
    (∑ x : ZMod (∏ j, p j), ‖tupleCRTFunction p hc g x‖ ^ 2) ≤ (∏ j, p j : ℕ) := by
  have he := (ZMod.prodEquivPi p hc).toEquiv.sum_comp
    (fun x : ∀ j, ZMod (p j) => ∏ j, ‖g j (x j)‖ ^ 2)
  change (∑ x : ZMod (∏ j, p j), ∏ j,
    ‖g j (ZMod.prodEquivPi p hc x j)‖ ^ 2) = _ at he
  calc
    _ = ∑ x : ∀ j, ZMod (p j), ∏ j, ‖g j (x j)‖ ^ 2 := by
      simpa only [tupleCRTFunction, norm_prod, Finset.prod_pow] using he
    _ = ∏ j, ∑ x : ZMod (p j), ‖g j x‖ ^ 2 := (Fintype.prod_sum (fun j (x : ZMod (p j)) => ‖g j x‖ ^ 2)).symm
    _ ≤ ∏ j, (p j : ℝ) := Finset.prod_le_prod
      (fun j _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (fun j _ => henergy j)
    _ = _ := (Nat.cast_prod _ _).symm

/-- The cofactor and outside-denominator units merely permute each local row. -/
theorem moving_crt_scaled_row_energy {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] [NeZero (∏ j, p j)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (g : ∀ j, ZMod (p j) → ℂ) (u : ∀ j, (ZMod (p j))ˣ)
    (henergy : ∀ j, (∑ x, ‖g j x‖ ^ 2) ≤ (p j : ℝ)) :
    (∑ x : ZMod (∏ j, p j),
      ‖tupleCRTFunction p hc (fun j x => g j ((u j : ZMod (p j)) * x)) x‖ ^ 2) ≤
        (∏ j, p j : ℕ) := by
  apply moving_crt_row_energy p hc
  intro j
  have he := Equiv.sum_comp (Equiv.mulLeft₀ (u j : ZMod (p j)) (Units.ne_zero _))
    (fun x => ‖g j x‖ ^ 2)
  exact he.trans_le (henergy j)

/-- This is the counting row indexed by `Fin modulus` in the finite transfer. -/
theorem moving_crt_fin_row_energy {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] [NeZero (∏ j, p j)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (g : ∀ j, ZMod (p j) → ℂ) (u : ∀ j, (ZMod (p j))ˣ)
    (henergy : ∀ j, (∑ x, ‖g j x‖ ^ 2) ≤ (p j : ℝ)) :
    (∑ x : Fin (∏ j, p j),
      ‖tupleCRTFunction p hc (fun j x => g j ((u j : ZMod (p j)) * x))
        (ZMod.finEquiv (∏ j, p j) x)‖ ^ 2) ≤ (∏ j, p j : ℕ) := by
  have he := (ZMod.finEquiv (∏ j, p j)).toEquiv.sum_comp
    (fun x => ‖tupleCRTFunction p hc (fun j x => g j ((u j : ZMod (p j)) * x)) x‖ ^ 2)
  change (∑ x : Fin (∏ j, p j),
    ‖tupleCRTFunction p hc (fun j x => g j ((u j : ZMod (p j)) * x))
      (ZMod.finEquiv (∏ j, p j) x)‖ ^ 2) = _ at he
  exact he.trans_le (moving_crt_scaled_row_energy p hc g u henergy)

/-- The giant factor is bounded by one; all other factors are the paper's
normalized compensation transforms. No bound on an individual compensation
transform is required. -/
theorem moving_crt_compensation_row_energy {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] [NeZero (∏ j, p j)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (giant : J)
    (g : ∀ j, ZMod (p j) → ℂ) (u : ∀ j, (ZMod (p j))ˣ)
    (S : ∀ j, Finset (ZMod (p j)))
    (hg : ∀ x, ‖g giant x‖ ≤ 1)
    (hregular : ∀ j, j ≠ giant → g j = normalizedResidueTransform (S j))
    (hS : ∀ j, j ≠ giant → (S j).Nonempty)
    (hSp : ∀ j, j ≠ giant → (S j).card < p j) :
    (∑ x : Fin (∏ j, p j),
      ‖tupleCRTFunction p hc (fun j x => g j ((u j : ZMod (p j)) * x))
        (ZMod.finEquiv (∏ j, p j) x)‖ ^ 2) ≤ (∏ j, p j : ℕ) := by
  apply moving_crt_fin_row_energy p hc g u
  intro j
  by_cases hj : j = giant
  · subst j
    calc
      (∑ x, ‖g giant x‖ ^ 2) ≤ ∑ _x : ZMod (p giant), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        nlinarith [hg x, norm_nonneg (g giant x)]
      _ = _ := by simp
  · rw [hregular j hj, normalizedResidueTransform_energy (S j) (hS j hj) (hSp j hj)]

private theorem finEquiv_eq_natCast (M : ℕ) [NeZero M] (x : Fin M) :
    ZMod.finEquiv M x = (x.val : ZMod M) := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M =>
    apply Fin.ext
    exact (Nat.mod_eq_of_lt x.isLt).symm

/-- The actual extracted row `G_P(t/d)`: each local argument includes the
outside denominator and the cofactor of that prime. Their inverses are units,
so the exact counting energy remains at most the modulus. -/
theorem moving_compensation_fourier_row_energy {J : Type*} [Fintype J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] [NeZero (∏ j, p j)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (giant : J)
    (g : ∀ j, ZMod (p j) → ℂ) (S : ∀ j, Finset (ZMod (p j)))
    (hg : ∀ x, ‖g giant x‖ ≤ 1)
    (hregular : ∀ j, j ≠ giant → g j = normalizedResidueTransform (S j))
    (hS : ∀ j, j ≠ giant → (S j).Nonempty)
    (hSp : ∀ j, j ≠ giant → (S j).card < p j)
    (D : ℕ) (hD : ∀ j, D.Coprime (p j)) :
    (∑ x : Fin (∏ j, p j), ‖∏ j,
      g j ((x.val : ZMod (p j)) / ((D * tupleCofactor p j : ℕ) : ZMod (p j)))‖ ^ 2) ≤
      (∏ j, p j : ℕ) := by
  let u : ∀ j, (ZMod (p j))ˣ := fun j =>
    (ZMod.unitOfCoprime (D * tupleCofactor p j)
      ((hD j).mul_left (tupleCofactor_coprime p hc j)))⁻¹
  have hh := moving_crt_compensation_row_energy p hc giant g u S hg hregular hS hSp
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x _
  congr 2
  unfold tupleCRTFunction
  apply Finset.prod_congr rfl
  intro j _
  simp only [u, Units.val_inv_eq_inv_val, ZMod.coe_unitOfCoprime,
    finEquiv_eq_natCast, map_natCast, Pi.natCast_apply, div_eq_mul_inv]
  rw [mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGuardedRow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The extracted row with the original support indicators -/

namespace Ostmann
open scoped Classical BigOperators

/-- Invalid compensation vectors stay in the original sample space with
zero row. No conditioning or renormalization of that sample law is used. -/
theorem movingGuardedRow_energy {J : Type*} [Fintype J]
    (q : J → ℕ) [∀ j, Fact (q j).Prime]
    (g : ∀ j, ZMod (q j) → ℂ) (D M : ℕ) (hM : (∏ j, q j) = M)
    (giant : J) (S : ∀ j, Finset (ZMod (q j)))
    (hg : ∀ x, ‖g giant x‖ ≤ 1)
    (hregular : ∀ j, j ≠ giant → g j = normalizedResidueTransform (S j))
    (hS : ∀ j, j ≠ giant → (S j).Nonempty)
    (hSp : ∀ j, j ≠ giant → (S j).card < q j) :
    (∑ t : Fin M, ‖movingGuardedRow q g D t‖ ^ 2) ≤ M := by
  by_cases h : Pairwise (fun i j => (q i).Coprime (q j)) ∧ (∀ j, D.Coprime (q j))
  · let : NeZero (∏ j, q j) := ⟨(Finset.prod_pos (fun j _ => (Fact.out : (q j).Prime).pos)).ne'⟩
    have he := moving_compensation_fourier_row_energy q h.1 giant g S hg hregular hS hSp D h.2
    rw [hM] at he
    simpa only [movingGuardedRow, ite_eq_left h, div_eq_mul_inv] using he
  · simp only [movingGuardedRow, ite_eq_right h, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, Nat.cast_nonneg]

/-- On support this is exactly the current transform at the grouped key. -/
theorem movingGuardedRow_grouped {J : Type*} [Fintype J]
    (q : J → ℕ) [∀ j, Fact (q j).Prime]
    (g : ∀ j, ZMod (q j) → ℂ) (D H : ℕ) (v : ℤ)
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (hD : ∀ j, D.Coprime (q j))
    (hH : H.Coprime (∏ j, q j)) :
    movingGuardedRow q g D (positiveIntegerPivotKey (∏ j, q j)
      (Finset.prod_pos (fun j _ => (Fact.out : (q j).Prime).pos)) H v) =
      movingRegularTransform q g (D * H) v := by
  rw [movingGuardedRow, ite_eq_left ⟨hc, hD⟩]
  have he := moving_regular_transform_grouped_key q g H D v hH
  simpa only [movingRegularTransform, Int.cast_natCast] using he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullTransformTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original full Fourier amplitude through one giant-only step -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.fullTransferSum_neZero
/-- The row used by Cauchy is the actual extracted part of the full transform.
The support conditions are used only where the original coefficient is nonzero. -/
theorem moving_full_transform_guarded {J H : Type*} [Fintype J] [Fintype H]
    (Q : J → ℕ) (L : H → ℕ) [∀ j, Fact (Q j).Prime] [∀ i, Fact (L i).Prime]
    (gQ : ∀ j, ZMod (Q j) → ℂ) (gL : ∀ i, ZMod (L i) → ℂ)
    (D M : ℕ) (hM : (∏ j, Q j) = M) (hMpos : 0 < M) (v : ℤ)
    (hQ : Pairwise (fun i j => (Q i).Coprime (Q j)))
    (hD : ∀ j, D.Coprime (Q j)) (hL : (∏ i, L i).Coprime M) :
    movingRegularTransform (Sum.elim Q L)
        (movingSumFactors Q L gQ gL) D v =
      movingGuardedRow Q gQ D (positiveIntegerPivotKey M hMpos (∏ i, L i) v) *
        movingRegularTransform L gL (M * D) v := by
  subst M
  rw [movingGuardedRow_grouped Q gQ D (∏ i, L i) v hQ hD hL]
  calc
    _ = movingRegularTransform Q gQ (D * ∏ i, L i) v *
        movingRegularTransform L gL (D * ∏ j, Q j) v := by
      convert moving_regular_transform_split Q L gQ gL D v using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext i
      cases i <;> rfl
    _ = _ := by rw [Nat.mul_comm (∏ j, Q j) D]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeTerms
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual diagonal and integer off-diagonal of a prime amplitude -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingOneGiant_transform_tagged {I : Type*} [Fintype I]
    (X : ℕ) (p : I → ℕ) [NeZero X] [∀ i, NeZero (p i)]
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingRegularTransform (movingOneGiantModuli X p)
      (movingOneGiantFactors X p greg ggiant favorable) D s =
    movingTaggedTransform (movingOneGiantModuli X p)
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s := by
  unfold movingRegularTransform movingTaggedTransform
  apply Finset.prod_congr rfl
  intro i _
  cases i <;> rfl

attribute [local instance] OAI.Ostmann.amplitudeSum_neZero
theorem movingOneGiant_pair_transform_tagged {I : Type*} [Fintype I]
    (X Y : ℕ) (p q : I → ℕ) [NeZero X] [NeZero Y]
    [∀ i, NeZero (p i)] [∀ i, NeZero (q i)]
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingRegularTransform (Sum.elim (movingOneGiantModuli X p) (movingOneGiantModuli Y q))
      (movingSumFactors (movingOneGiantModuli X p) (movingOneGiantModuli Y q)
        (movingOneGiantFactors X p greg ggiant favorable)
        (movingOneGiantFactors Y q greg ggiant favorable)) D s =
    movingTaggedTransform (Sum.elim (movingOneGiantModuli X p) (movingOneGiantModuli Y q))
      (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
        (Sum.elim (fun _ : Unit => true) (fun _ => false))) greg ggiant favorable D s := by
  unfold movingRegularTransform movingTaggedTransform
  apply Finset.prod_congr rfl
  intro i _
  rcases i with (i | i) <;> cases i <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationProductBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual compensation-prior support bounds for the first transfers -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingCompensation_product_lower {σ : Type*} (value : σ → ℕ)
    (μ : σ → ℝ) (c : ℝ)
    (hlower : ∀ x, μ x ≠ 0 → Real.exp (c - 1) ≤ (value x : ℝ))
    (n : ℕ) (a : TreeLeafTuple (Fin 4 → σ) n)
    (ha : movingCompensationPrior μ n a ≠ 0) :
    Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * (c - 1)) ≤
      (MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a)) : ℝ) := by
  induction n with
  | zero =>
    change Real.exp (4 * (c - 1)) ≤
      (MovingSlotReversal.naturalProduct value (List.ofFn a) : ℝ)
    have hprod : (∏ i : Fin 4, Real.exp (c - 1)) ≤ ∏ i : Fin 4, (value (a i) : ℝ) :=
      Finset.prod_le_prod (fun _ _ => Real.exp_nonneg _)
        (fun i hi => hlower _ (Finset.prod_ne_zero_iff.mp ha i hi))
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_nat_mul, MovingSlotReversal.naturalProduct,
      List.map_ofFn, List.prod_ofFn, Function.comp_def, Nat.cast_prod, Nat.cast_ofNat] using hprod
  | succ n ih =>
    have hL := ih a.1 (left_ne_zero_of_mul ha)
    have hR := ih a.2 (right_ne_zero_of_mul ha)
    change Real.exp (((2 ^ (n + 1) * 4 : ℕ) : ℝ) * (c - 1)) ≤
      (MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a.1) ++
          flattenMovingSlots n (movingCompensationSlots n a.2)) : ℝ)
    rw [movingNaturalProduct_append]
    simp only [Nat.cast_mul] at hL hR ⊢
    calc
      _ = Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * (c - 1)) *
          Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * (c - 1)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        rw [pow_succ]
        ring
      _ ≤ _ := by
        simpa only [Nat.cast_mul] using
          mul_le_mul hL hR (Real.exp_nonneg _) (Nat.cast_nonneg _)

theorem movingInsertedPivot_product_lower {σ : Type*} (value : σ → ℕ)
    (μ : σ → ℝ) (c G : ℝ) (φ : ℝ → ℝ)
    (hlower : ∀ x, μ x ≠ 0 → Real.exp (c - 1) ≤ (value x : ℝ))
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (n : ℕ) (a : TreeLeafTuple (Fin 4 → σ) n)
    (ha : movingCompensationPrior μ n a ≠ 0)
    (p : ℕ) (hp : 0 < p) (hφ : φ (Real.log p - G) ≠ 0) :
    Real.exp (G - 1 + ((2 ^ n * 4 : ℕ) : ℝ) * (c - 1)) ≤
      (p * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a)) : ℕ) := by
  have habs : |Real.log p - G| < 1 := by
    by_contra hn
    exact hφ (hout _ (not_lt.mp hn))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpbound : Real.exp (G - 1) ≤ (p : ℝ) := by
    have hlog : G - 1 ≤ Real.log (p : ℝ) := by linarith [(abs_lt.mp habs).1]
    exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hpR)
  rw [Real.exp_add]
  simpa only [Nat.cast_mul] using
    mul_le_mul hpbound (movingCompensation_product_lower value μ c hlower n a ha)
      (Real.exp_nonneg _) (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInitialCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal level-zero coefficient and its original cutoff -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingFrequencyCoefficient_levelZero_sample (σ : Type) [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (small bulk : List σ) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 s
      small bulk XL XR =
    movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) 0 s small bulk XL XR := by
  unfold movingFrequencyCoefficient
  change (∑ t : Unit, _) = _
  rw [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem movingFrequencyCoefficient_levelZero (σ : Type) [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (small bulk : List σ) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 s
      small bulk XL XR =
    movingGuardedLeaf value outside F ⟨0, .leaf s (small ++ bulk), XL, XR⟩ s := by
  unfold movingFrequencyCoefficient
  change (∑ t : Unit, _) = _
  rw [Finset.univ_unique, Finset.sum_singleton]
  unfold movingSupportedSampledWeight movingSampledWeight
  rw [← (movingSampleZeroEquiv σ).sum_comp]
  rw [Finset.univ_unique, Finset.sum_singleton]
  simp [movingSampleZeroEquiv, movingSamplesPrior, recursiveTransferWeight,
    buildMovingSlotData, frequencyRoot, flattenMovingSlots, movingRootedFrequencyTree]

theorem movingFrequencyCoefficient_levelZero_support (σ : Type) [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (small bulk : List σ) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 s
      small bulk XL XR ≠ 0) :
    F ⟨0, .leaf s (small ++ bulk), XL, XR⟩ s ≠ 0 := by
  rw [movingFrequencyCoefficient_levelZero] at h
  unfold movingGuardedLeaf at h
  split_ifs at h
  · exact h
  · exact (h rfl).elim

theorem movingOriginalLeaf_window {σ I : Type*}
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) (s : ℤ)
    (h : movingOriginalLeaf value q F g Dq S ψ X lo hi x s ≠ 0) :
    (movingSlotModulus value x : ℝ) / X ∈ Set.Icc lo hi := by
  have hw : movingWindowLeaf value X lo hi (movingDataLeaf F) x s ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul h)
  unfold movingWindowLeaf at hw
  split_ifs at hw with hc
  · exact hc
  · exact (hw rfl).elim

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingEarlyCellCaps
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete product caps for the first two integer extensions -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingCompensation_pivot_lower_of_bound {σ : Type*} (value : σ → ℕ)
    (μ : σ → ℝ) (c G : ℝ)
    (hlower : ∀ x, μ x ≠ 0 → Real.exp (c - 1) ≤ (value x : ℝ))
    (n : ℕ) (a : TreeLeafTuple (Fin 4 → σ) n)
    (ha : movingCompensationPrior μ n a ≠ 0) (p : ℕ)
    (hp : Real.exp (G - 1) ≤ (p : ℝ)) :
    Real.exp (G - 1 + ((2 ^ n * 4 : ℕ) : ℝ) * (c - 1)) ≤
      (p * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a)) : ℕ) := by
  rw [Real.exp_add]
  simpa only [Nat.cast_mul] using
    mul_le_mul hp (movingCompensation_product_lower value μ c hlower n a ha)
      (Real.exp_nonneg _) (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveProductBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product windows inherited through every actual integer extension -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

private theorem remove_positive_product (A B : ℕ) (T E : ℝ)
    (hA : Real.exp T ≤ (A : ℝ)) (hAB : ((A * B : ℕ) : ℝ) ≤ Real.exp E) :
    (B : ℝ) ≤ Real.exp (E - T) := by
  rw [Nat.cast_mul] at hAB
  rw [Real.exp_sub]
  apply (le_div_iff₀ (Real.exp_pos T)).mpr
  have hh := (mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg B)).trans hAB
  simpa only [Nat.cast_mul, mul_comm] using hh

theorem movingNaturalProduct_append_leaves {σ : Type*} (value : σ → ℕ)
    (n : ℕ) (u small bulk : TreeLeafTuple (List σ) n) :
    MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n (appendMovingSlotLeaves n u small) ++ flattenMovingSlots n bulk) =
      MovingSlotReversal.naturalProduct value (flattenMovingSlots n u) *
        MovingSlotReversal.naturalProduct value
          (flattenMovingSlots n small ++ flattenMovingSlots n bulk) := by
  have hp := ((flattenMovingSlots_append_perm n u small).append_right
    (flattenMovingSlots n bulk)).map value
  change (List.map value _).prod = _
  rw [hp.prod_eq]
  simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]
  ring

/-- This bound is proved on the original sampled histories, before summing any
frequencies. The inserted giants may be arbitrary positive integers. -/
theorem movingSupportedSampledWeight_product_bound {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (T : ℕ → ℝ) (W : ℝ)
    (hF : ∀ s small XL XR,
      F ⟨0, .leaf s small, XL, XR⟩ s ≠ 0 →
        ((XL * XR * MovingSlotReversal.naturalProduct value small : ℕ) : ℝ) ≤ Real.exp W)
    (hmin : ∀ n (a : TreeLeafTuple (Fin 4 → σ) n),
      movingCompensationPrior (μ n) n a ≠ 0 → ∀ p : ℕ, 0 < p →
      φ (Real.log p - G (n + 1)) ≠ 0 →
      Real.exp (T n) ≤ (p * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a)) : ℕ))
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ)
    (h : movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n t small bulk XL XR ≠ 0) :
    ((XL * XR * MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) : ℕ) : ℝ) ≤
        Real.exp (movingProductExponent T W n) := by
  induction n generalizing XL XR with
  | zero =>
    change List σ at small bulk
    change ℤ at t
    have hh := movingFrequencyCoefficient_levelZero_support σ value outside μ childBound pivotBound
      (fun _ => 0) F φ G t small bulk XL XR
      (by rwa [movingFrequencyCoefficient_levelZero_sample])
    exact hF t (small ++ bulk) XL XR hh
  | succ n ih =>
    rw [movingSupportedSampledWeight_direct_node] at h
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    dsimp only at ha
    have hm : movingCompensationPrior (μ n) n a ≠ 0 := by
      intro hz
      exact ha (by rw [hz, Complex.ofReal_zero, zero_mul])
    have hb := right_ne_zero_of_mul ha
    split_ifs at hb with hg
    · let u := movingCompensationSlots n a
      let p := movingTopPivot value
        (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)
        (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)
        (flattenMovingSlots n u) XL XR t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      have hp : 0 < p := Nat.pos_of_mul_pos_right hg.2.1.pivot_pos
      have hphi : φ (Real.log p - G (n + 1)) ≠ 0 := by
        intro hz
        apply left_ne_zero_of_mul (left_ne_zero_of_mul hb)
        change (((MovingSlotReversal.naturalProduct value (flattenMovingSlots n u) : ℝ) *
          φ (Real.log p - G (n + 1)) : ℝ) : ℂ) = 0
        rw [hz, mul_zero, Complex.ofReal_zero]
      have hl := ih t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 p XL
        (right_ne_zero_of_mul (left_ne_zero_of_mul hb))
      have hr := ih t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 p XR
        (star_ne_zero.mp (right_ne_zero_of_mul hb))
      rw [movingNaturalProduct_append_leaves] at hl hr
      let U := MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
      let L := XL * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)
      let R := XR * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)
      have hidL : p * XL * (U * MovingSlotReversal.naturalProduct value
          (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)) = (p * U) * L := by
        dsimp only [L]; ring
      have hidR : p * XR * (U * MovingSlotReversal.naturalProduct value
          (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)) = (p * U) * R := by
        dsimp only [R]; ring
      rw [hidL] at hl
      rw [hidR] at hr
      have hlow := hmin n a hm p hp hphi
      have hl' := remove_positive_product (p * U) L (T n) _ hlow hl
      have hr' := remove_positive_product (p * U) R (T n) _ hlow hr
      have hprod := mul_le_mul hl' hr' (Nat.cast_nonneg R) (Real.exp_nonneg _)
      have hid : XL * XR * MovingSlotReversal.naturalProduct value
          (flattenMovingSlots (n + 1) small ++ flattenMovingSlots (n + 1) bulk) = L * R := by
        simp only [flattenMovingSlots, movingNaturalProduct_append, L, R]
        ring
      rw [hid, Nat.cast_mul]
      convert hprod using 1
      all_goals try with_reducible_and_instances rfl
      rw [movingProductExponent, ← Real.exp_add]
      congr 1
      ring
    · exact (hb rfl).elim

/-- Summing descendants cannot create support outside the inherited product
window. This is the coefficient used by the original arithmetic comparison. -/
theorem movingFrequencyCoefficient_recursive_product_bound {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi W : ℝ) (hX : 0 < X) (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G T : ℕ → ℝ)
    (hmin : ∀ n (a : TreeLeafTuple (Fin 4 → σ) n),
      movingCompensationPrior (μ n) n a ≠ 0 → ∀ p : ℕ, 0 < p →
      φ (Real.log p - G (n + 1)) ≠ 0 →
      Real.exp (T n) ≤ (p * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingCompensationSlots n a)) : ℕ))
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small bulk XL XR ≠ 0) :
    ((XL * XR * MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) : ℕ) : ℝ) ≤
        Real.exp (movingProductExponent T W n) := by
  unfold movingFrequencyCoefficient at h
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  apply movingSupportedSampledWeight_product_bound value outside μ childBound pivotBound
    (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G T W _ hmin n _ small bulk XL XR ht
  intro s small XL XR hh
  have hw := movingOriginalLeaf_window value q F g Dq S ψ X lo hi
    ⟨0, .leaf s small, XL, XR⟩ s hh
  have hu := (div_le_iff₀ hX).mp hw.2
  have hu' : ((XL * XR * MovingSlotReversal.naturalProduct value small : ℕ) : ℝ) ≤ X * hi := by
    simpa only [movingSlotModulus, mul_comm] using hu
  exact hu'.trans hwindow

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveTemplateCaps
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derived product caps for every restored moving template -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- Every compensation prior is the original prior. Only its actual nonzero
support is used in the lower bound; no renormalization is performed. -/
theorem movingFrequencyCoefficient_recursive_cell_cap {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμ : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n : ℕ) (a : TreeLeafTuple (Fin 4 → σ) n)
    (ha : movingCompensationPrior (μ n) n a ≠ 0)
    (s : ℤ) (small bulk : TreeLeafTuple (List σ) n) (p XR : ℕ)
    (hpbound : Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s
      (appendMovingSlotLeaves n (movingCompensationSlots n a) small) bulk p XR ≠ 0) :
    XR * MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) ≤
      ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
        movingCellPivotExponent G c n)⌉₊ := by
  let T := movingCellPivotExponent G c
  have hmin (j : ℕ) (b : TreeLeafTuple (Fin 4 → σ) j)
      (hb : movingCompensationPrior (μ j) j b ≠ 0) (p' : ℕ) (hp' : 0 < p')
      (hφ' : φ (Real.log p' - G (j + 1)) ≠ 0) :=
    movingInsertedPivot_product_lower value (μ j) (c j) (G (j + 1)) φ
      (hμ j) hout j b hb p' hp' hφ'
  have hb := movingFrequencyCoefficient_recursive_product_bound value outside μ
    childBound pivotBound V q F g Dq S ψ X lo hi W hX hwindow φ G T hmin n s
    (appendMovingSlotLeaves n (movingCompensationSlots n a) small) bulk p XR h
  rw [movingNaturalProduct_append_leaves] at hb
  let U := MovingSlotReversal.naturalProduct value
    (flattenMovingSlots n (movingCompensationSlots n a))
  let R := XR * MovingSlotReversal.naturalProduct value
    (flattenMovingSlots n small ++ flattenMovingSlots n bulk)
  have hid : p * XR * (U * MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk)) = (p * U) * R := by
    dsimp only [R]; ring
  rw [hid, Nat.cast_mul] at hb
  have hlow := movingCompensation_pivot_lower_of_bound value (μ n) (c n) (G (n + 1))
    (hμ n) n a ha p hpbound
  have hreal : (R : ℝ) ≤ Real.exp (movingProductExponent T W n - T n) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have hh := (mul_le_mul_of_nonneg_right hlow (Nat.cast_nonneg R)).trans hb
    simpa only [T, movingCellPivotExponent, mul_comm] using hh
  exact_mod_cast hreal.trans (Nat.le_ceil _)

/-- The product bound required by the Cauchy--Schwarz transfer now follows at
any depth from the terminal cutoff and the selected compensation cells. -/
theorem movingTemplateCoefficient_recursive_cell_cap {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμ : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n r m : ℕ) (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
    (s : ℤ) (y : MovingRegularSlot n r m → σ) (p XR : ℕ)
    (hpbound : Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m s
      (movingRestoreSample n r m u y) p XR ≠ 0) :
    XR * (∏ i, value (y i)) ≤
      ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
        movingCellPivotExponent G c n)⌉₊ := by
  let a := (movingTemplateCompensationEquiv σ n).symm u
  have he : movingTemplateCompensationEquiv σ n a = u := Equiv.apply_symm_apply _ _
  have ha : movingCompensationPrior (μ n) n a ≠ 0 := by
    rw [← movingTemplateCompensationEquiv_prior, he]
    exact hu
  rw [← he, movingTemplateCoefficient_restored] at h
  have hc := movingFrequencyCoefficient_recursive_cell_cap value outside μ childBound pivotBound V
    q F g Dq S ψ X lo hi W hX hwindow φ G c hout hμ n a ha s _ _ p XR hpbound h
  rwa [movingTemplateMapped_product] at hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingProductFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer frequency cutoffs that retain the actual product-window center -/
namespace Ostmann

theorem movingProductExponent_monotone (T : ℕ → ℝ) (W : ℝ)
    (hgap : ∀ n, 2 * T n ≤ movingProductExponent T W n) :
    Monotone (movingProductExponent T W) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [movingProductExponent]
  linarith [hgap n]

theorem movingProductNaturalCutoff_monotone (T : ℕ → ℝ) (W Y m : ℝ)
    (hgap : ∀ n, 2 * T n ≤ movingProductExponent T W n) :
    Monotone (movingProductNaturalCutoff T W Y m) := by
  intro i j hij
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  have hE := movingProductExponent_monotone T W hgap hij
  have hpow : (2 : ℝ) ^ i ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hij
  have hs := mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg (4 * m))
  dsimp only [movingProductFrequencyExponent]
  linarith

theorem movingProductFrequency_reserve (T : ℕ → ℝ) (W Y m : ℝ) (n : ℕ) :
    movingProductFrequencyExponent T W Y m (n + 1) -
      (movingProductFrequencyExponent T W Y m n + movingProductExponent T W n - 2 * T n) =
      (2 : ℝ) ^ n * Real.sqrt (4 * m) := by
  simp only [movingProductFrequencyExponent, movingProductExponent, pow_succ]
  ring

/-- The full ceiling product cap satisfies the next integer-frequency bound.
Only the actual lower bound on the inserted pivot product is needed. -/
theorem movingProductNaturalCutoff_scale (T : ℕ → ℝ) (W Y m : ℝ) (n : ℕ)
    (hm : 64 ≤ m) (hY : Y ≤ W)
    (hgap : ∀ j, 2 * T j ≤ movingProductExponent T W j)
    (hH : 0 ≤ movingProductExponent T W n - T n)
    (M : ℕ) (hM : Real.exp (T n) ≤ (M : ℝ)) :
    2 * movingProductNaturalCutoff T W Y m n *
        ⌈Real.exp (movingProductExponent T W n - T n)⌉₊ ≤
      movingProductNaturalCutoff T W Y m (n + 1) * M := by
  let E := movingProductExponent T W n
  let F := movingProductFrequencyExponent T W Y m n
  let F' := movingProductFrequencyExponent T W Y m (n + 1)
  have hroot : 8 ≤ Real.sqrt (4 * m) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hpow : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hpow' : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hE' : W ≤ movingProductExponent T W (n + 1) :=
    movingProductExponent_monotone T W hgap (Nat.zero_le _)
  have hF' : Real.log 2 ≤ F' := by
    dsimp only [F', movingProductFrequencyExponent]
    nlinarith [Real.sqrt_nonneg (4 * m)]
  have hreserve := movingProductFrequency_reserve T W Y m n
  have hmargin : Real.log 4 + F + E - T n ≤ F' + T n - Real.log 2 := by
    dsimp only [F, F', E] at *
    nlinarith [Real.sqrt_nonneg (4 * m)]
  have hHceil : (⌈Real.exp (E - T n)⌉₊ : ℝ) ≤ 2 * Real.exp (E - T n) := by
    have hc := (Nat.ceil_lt_add_one (Real.exp_pos (E - T n)).le).le
    have he := Real.one_le_exp hH
    dsimp only [E] at *
    linarith
  have hV : (movingProductNaturalCutoff T W Y m n : ℝ) ≤ Real.exp F :=
    Nat.floor_le (Real.exp_pos F).le
  have hV' : Real.exp F' / 2 ≤ (movingProductNaturalCutoff T W Y m (n + 1) : ℝ) := by
    have hh := (natural_exp_cutoff_bounds F' hF').2.2
    change Real.exp F' ≤ 2 * (movingProductNaturalCutoff T W Y m (n + 1) : ℝ) at hh
    linarith
  have hscaled : (2 : ℝ) * movingProductNaturalCutoff T W Y m n *
      (⌈Real.exp (E - T n)⌉₊ : ℝ) ≤
        (movingProductNaturalCutoff T W Y m (n + 1) : ℝ) * M := by
    calc
      _ ≤ (2 * Real.exp F) * (2 * Real.exp (E - T n)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hV (by norm_num)) hHceil
          (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (Real.log 4 + F + E - T n) := by
        rw [show Real.log 4 + F + E - T n = Real.log 4 + (F + (E - T n)) by ring,
          Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        ring
      _ ≤ Real.exp (F' + T n - Real.log 2) := Real.exp_le_exp.mpr hmargin
      _ = (Real.exp F' / 2) * Real.exp (T n) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        ring
      _ ≤ _ := mul_le_mul hV' hM (Real.exp_nonneg _) (Nat.cast_nonneg _)
  exact_mod_cast hscaled

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual compensation tuple satisfies the integer frequency scale -/
namespace Ostmann
open scoped Classical BigOperators

/-- This discharges the scale premise for the original, unconditioned
compensation draw and every integer in the full outer cell. -/
theorem movingProductNaturalCutoff_compensation_scale {σ : Type} [Fintype σ]
    (value : σ → ℕ) (μ : ℕ → σ → ℝ) (G c : ℕ → ℝ)
    (hμ : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (W Y m : ℝ) (hm : 64 ≤ m) (hY : Y ≤ W)
    (hgap : ∀ j, 2 * movingCellPivotExponent G c j ≤
      movingProductExponent (movingCellPivotExponent G c) W j)
    (n : ℕ) (hH : 0 ≤ movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)
    (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
    (p : ℕ) (hp : Real.exp (G (n + 1) - 1) ≤ (p : ℝ)) :
    2 * movingProductNaturalCutoff (movingCellPivotExponent G c) W Y m n *
      ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
        movingCellPivotExponent G c n)⌉₊ ≤
      movingProductNaturalCutoff (movingCellPivotExponent G c) W Y m (n + 1) *
        (p * ∏ i, value (u i)) := by
  let a := (movingTemplateCompensationEquiv σ n).symm u
  have he : movingTemplateCompensationEquiv σ n a = u := Equiv.apply_symm_apply _ _
  have ha : movingCompensationPrior (μ n) n a ≠ 0 := by
    rw [← movingTemplateCompensationEquiv_prior, he]
    exact hu
  have hlower := movingCompensation_pivot_lower_of_bound value (μ n) (c n) (G (n + 1))
    (hμ n) n a ha p hp
  rw [movingTemplateCompensationEquiv_product, he] at hlower
  exact movingProductNaturalCutoff_scale (movingCellPivotExponent G c) W Y m n hm hY
    hgap hH (p * ∏ i, value (u i)) hlower

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularLiveOffDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The transfer only tests live retained primes -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.liveCopiedSum_neZero
/-- The original coefficient and all its prior factors remain in `W`.
Only the local Fourier arguments are rewritten; no absolute values are
taken and no integer-pivot transform is introduced. -/
theorem movingGiantOffDiagonal_regular_on_live {A H : Type*} [Fintype A] [Fintype H]
    (L : A → H → ℕ) [∀ a i, Fact (L a i).Prime]
    (g : ∀ a i, ZMod (L a i) → ℂ)
    (hg : ∀ a i x, g a i (-x) = conj (g a i x))
    (I : Finset ℕ) (V U D : ℕ) (v : A → ℤ) (w : ℕ → ℝ) (W : ℕ → A → ℂ)
    (hsupport : ∀ p ∈ I, ∀ a, W p a ≠ 0 →
      Pairwise (fun i j => (L a i).Coprime (L a j)) ∧
      (∏ i, L a i).Coprime (p * U) ∧ ∀ i, D.Coprime (L a i))
    (hlarge : ∀ p ∈ I, ∀ a, W p a ≠ 0 →
      ∀ q, q.Prime → q ∣ ∏ i, L a i → V < q) :
    movingGiantOffDiagonal I V U (fun a => ∏ i, L a i) v w
      (movingRegularCoefficient L g D U v W) =
    ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
      if validTransferredPivot I (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U) then
        let p := reconstructedPivot (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U)
        (w p : ℂ) * W p a * conj (W p b) *
          movingRegularTransform (Sum.elim (L a) (L b))
            (fun i => match i with | .inl j => g a j | .inr j => g b j) D s
      else 0 := by
  unfold movingGiantOffDiagonal
  apply Finset.sum_congr rfl
  intro s hsV
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with hvalid
  · let p := reconstructedPivot (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U)
    change (w p : ℂ) * movingRegularCoefficient L g D U v W p a *
      conj (movingRegularCoefficient L g D U v W p b) =
        (w p : ℂ) * W p a * conj (W p b) * _
    by_cases ha : W p a = 0
    · simp only [movingRegularCoefficient, ha, zero_mul, mul_zero]
    by_cases hb : W p b = 0
    · simp only [movingRegularCoefficient, hb, zero_mul, map_zero, mul_zero]
    have hp : p ∈ I := hvalid.2.2.2
    obtain ⟨hpa, hMa, hDa⟩ := hsupport p hp a ha
    obtain ⟨hpb, hMb, hDb⟩ := hsupport p hp b hb
    have hs : s ≠ 0 := left_ne_zero_of_mul hvalid.1
    have hrel : v a * (∏ i, L b i) - v b * (∏ i, L a i) =
        s * ((p * U : ℕ) : ℤ) := by
      have he := validTransferredPivot_equation I _ _ hvalid
      calc
        _ = (s * (U : ℤ)) * (p : ℤ) := he
        _ = _ := by push_cast; ring
    have hAB := transferred_products_coprime (∏ i, L a i) (∏ i, L b i)
      (v a) (v b) s (p * U) hs hrel
      (fun q hq hqa _ => ((mem_transferFrequencyRange V s).mp hsV).trans_lt
        (hlarge p hp a ha q hq hqa))
      (common_prime_pivot_unit (p * U) _ _ hMa)
    have hcross (i j : H) : (L a i).Coprime (L b j) :=
      (hAB.coprime_dvd_left (Finset.dvd_prod_of_mem (L a) (Finset.mem_univ i))).coprime_dvd_right
        (Finset.dvd_prod_of_mem (L b) (Finset.mem_univ j))
    have hcop : Pairwise (fun i j =>
        (Sum.elim (L a) (L b) i).Coprime (Sum.elim (L a) (L b) j)) := by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact hpa (fun he => hij (congrArg Sum.inl he))
        | inr j => exact hcross i j
      | inr i =>
        cases j with
        | inl j => exact (hcross j i).symm
        | inr j => exact hpb (fun he => hij (congrArg Sum.inr he))
    have hM : ∀ i, (p * U).Coprime (Sum.elim (L a) (L b) i) := by
      intro i
      cases i with
      | inl i => exact hMa.symm.coprime_dvd_right (Finset.dvd_prod_of_mem (L a) (Finset.mem_univ i))
      | inr i => exact hMb.symm.coprime_dvd_right (Finset.dvd_prod_of_mem (L b) (Finset.mem_univ i))
    have hD : ∀ i, D.Coprime (Sum.elim (L a) (L b) i) := by
      intro i
      cases i with
      | inl i => exact hDa i
      | inr i => exact hDb i
    have he := moving_regular_transform_transfer (L a) (L b) (g a) (g b) (hg b)
      (p * U) D (v a) (v b) s hcop hM hD hrel
    simp only [movingRegularCoefficient, map_mul (starRingEnd ℂ)]
    calc
      _ = ((w p : ℂ) * W p a * conj (W p b)) *
          (movingRegularTransform (L a) (g a) (p * U * D) (v a) *
            conj (movingRegularTransform (L b) (g b) (p * U * D) (v b))) := by ring
      _ = _ := by
        rw [he]
        congr 1
        unfold movingRegularTransform
        apply Finset.prod_congr rfl
        intro i _
        cases i <;> rfl
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantSupportedTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original giant-only transfer, including its exact diagonal -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The entire Cauchy--Schwarz, positive-integer extension and forced-pivot
substitution. The inherited prime laws remain in `μ` and `c`; the integer
variable has no prime-specific transform attached to it. -/
theorem moving_giant_transfer_on_prior {Y A : Type*} [Fintype Y] [Fintype A]
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (hI : ∀ p ∈ I, 0 < p)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμmass : ∑ y, μ y = 1)
    (w : ℕ → ℝ) (hw : ∀ p ∈ I, 0 ≤ w p) (Z : ℝ) (hZ : 0 ≤ Z)
    (hmass : ∑ p : P, Z * w p / (p : ℝ) = 1)
    (U : Y → ℕ) (hU : ∀ y, 0 < U y)
    (row : ∀ y, (p : P) → Fin ((p : ℕ) * U y) → ℂ)
    (hrow : ∀ y p, (∑ t, ‖row y p t‖ ^ 2) ≤ (p : ℕ) * (U y : ℝ))
    (L : Y → A → ℕ) (v : Y → A → ℤ) (c : Y → ℕ → A → ℂ)
    (hcoprime : ∀ y p, p ∈ I → ∀ a, c y p a ≠ 0 → (L y a).Coprime (p * U y))
    (N H V : ℕ)
    (hv : ∀ y p, p ∈ I → ∀ a, c y p a ≠ 0 → (v y a).natAbs ≤ N)
    (hL : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → ∀ a, c y p a ≠ 0 → L y a ≤ H)
    (hscale : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → 2 * N * H ≤ V * (p * U y)) :
    ‖∑ y, (μ y : ℂ) * ∑ p : P, ((Z * w p / (p : ℝ) : ℝ) : ℂ) *
      ∑ a, row y p (positiveIntegerPivotKey _
        (Nat.mul_pos (hP p p.property).pos (hU y)) (L y a) (v y a)) * c y p a‖ ^ 2 ≤
      Z * ((∑ y, μ y * (U y : ℝ) *
        ∑ p ∈ I, w p * (pivotDiagonal (L y) (v y) (c y p)).re) +
        (∑ y, ((μ y * (U y : ℝ) : ℝ) : ℂ) *
          movingGiantOffDiagonal I V (U y) (L y) (v y) w (c y)).re) := by
  let B : ∀ y p, Fin (p * U y) → ℂ := fun y p =>
    if hp : 0 < p * U y then
      groupedCoefficient (fun a => positiveIntegerPivotKey _ hp (L y a) (v y a)) (c y p)
    else fun _ => 0
  have ht := moving_prime_row_transfer P I hP hPI μ hμ hμmass w hw Z hZ hmass U row B hrow
  have hleft : (∑ y, (μ y : ℂ) * ∑ p : P, ((Z * w p / (p : ℝ) : ℝ) : ℂ) *
      ∑ t, row y p t * B y p t) =
      ∑ y, (μ y : ℂ) * ∑ p : P, ((Z * w p / (p : ℝ) : ℝ) : ℂ) *
      ∑ a, row y p (positiveIntegerPivotKey _
        (Nat.mul_pos (hP p p.property).pos (hU y)) (L y a) (v y a)) * c y p a := by
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    simp only [B, dite_eq_left (Nat.mul_pos (hP p p.property).pos (hU y))]
    exact (pivot_residue_grouping _ (row y p) (c y p)).symm
  rw [hleft] at ht
  apply ht.trans_eq
  congr 1
  have hs (y : Y) (hy : μ y ≠ 0) :
      (∑ p ∈ I, w p * ∑ t, ‖B y p t‖ ^ 2) =
        (∑ p ∈ I, w p * (pivotDiagonal (L y) (v y) (c y p)).re) +
          (movingGiantOffDiagonal I V (U y) (L y) (v y) w (c y)).re := by
    have hsplit (p : ℕ) (hp : p ∈ I) : (∑ t, ‖B y p t‖ ^ 2) =
        (pivotDiagonal (L y) (v y) (c y p)).re +
        (pivotOffDiagonal (p * U y) (L y) (v y) (c y p)).re := by
      have hpU := Nat.mul_pos (hI p hp) (hU y)
      let : NeZero (p * U y) := ⟨hpU.ne'⟩
      simpa only [B, dite_eq_left hpU, positiveIntegerPivotKey] using
        pivot_square_split_on_support (p * U y) (L y) (v y) (c y p) (hcoprime y p hp)
    calc
      _ = ∑ p ∈ I, w p * ((pivotDiagonal (L y) (v y) (c y p)).re +
          (pivotOffDiagonal (p * U y) (L y) (v y) (c y p)).re) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hsplit p hp]
      _ = (∑ p ∈ I, w p * (pivotDiagonal (L y) (v y) (c y p)).re) +
          (∑ p ∈ I, (w p : ℂ) * pivotOffDiagonal (p * U y) (L y) (v y) (c y p)).re := by
        simp only [mul_add, Finset.sum_add_distrib, Complex.re_sum,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      _ = _ := by rw [movingGiantOffDiagonal_eq I hI (U y) (hU y) N H V
        (L y) (v y) w (c y) (hv y) (hL y hy) (hscale y hy)]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : μ y = 0
  · simp only [hy, zero_mul, zero_add]
  · rw [hs y hy, mul_add]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantSupportedTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

/-- The actual normalizer of (7.3), not a factorial or an assumed transfer
loss, gives the loss in (7.13). The off-diagonal on the right is the exact
weighted positive-integer substitution. -/
theorem smoothGiantPrior_transfer_on_prior {Y A : Type*} [Fintype Y] [Fintype A]
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (hI : ∀ p ∈ I, 0 < p)
    (φ : ℝ → ℝ) (G : ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass P φ G)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμmass : ∑ y, μ y = 1)
    (U : Y → ℕ) (hU : ∀ y, 0 < U y)
    (row : ∀ y, (p : P) → Fin ((p : ℕ) * U y) → ℂ)
    (hrow : ∀ y p, (∑ t, ‖row y p t‖ ^ 2) ≤ (p : ℕ) * (U y : ℝ))
    (L : Y → A → ℕ) (v : Y → A → ℤ) (c : Y → ℕ → A → ℂ)
    (hcoprime : ∀ y p, p ∈ I → ∀ a, c y p a ≠ 0 → (L y a).Coprime (p * U y))
    (N H V : ℕ)
    (hv : ∀ y p, p ∈ I → ∀ a, c y p a ≠ 0 → (v y a).natAbs ≤ N)
    (hL : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → ∀ a, c y p a ≠ 0 → L y a ≤ H)
    (hscale : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → 2 * N * H ≤ V * (p * U y)) :
    Real.exp (-smoothGiantLogNormalizer P φ G) *
      ‖∑ y, (μ y : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
        ∑ a, row y p (positiveIntegerPivotKey _
          (Nat.mul_pos (hP p p.property).pos (hU y)) (L y a) (v y a)) * c y p a‖ ^ 2 ≤
      (∑ y, μ y * (U y : ℝ) *
        ∑ p ∈ I, φ (Real.log p - G) * (pivotDiagonal (L y) (v y) (c y p)).re) +
      ‖∑ y, ((μ y * (U y : ℝ) : ℝ) : ℂ) *
        movingGiantOffDiagonal I V (U y) (L y) (v y)
          (fun p => φ (Real.log p - G)) (c y)‖ := by
  have ht := moving_giant_transfer_on_prior P I hP hPI hI μ hμ hμmass
    (fun p => φ (Real.log p - G)) (fun _ _ => hφ _)
    (Real.exp (smoothGiantLogNormalizer P φ G)) (Real.exp_nonneg _)
    (smoothGiantPrior_mass P φ G hpos) U hU row hrow L v c hcoprime N H V hv hL hscale
  change ‖∑ y, (μ y : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
    ∑ a, row y p (positiveIntegerPivotKey _
      (Nat.mul_pos (hP p p.property).pos (hU y)) (L y a) (v y a)) * c y p a‖ ^ 2 ≤ _ at ht
  have hh := mul_le_mul_of_nonneg_left ht
    (Real.exp_nonneg (-smoothGiantLogNormalizer P φ G))
  rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hh
  exact hh.trans (add_le_add le_rfl (Complex.re_le_norm _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullLiveTransformTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.liveFullTransferSum_neZero
theorem smoothGiantPrior_full_transform_transfer_on_live
    {Y A J H : Type*} [Fintype Y] [Fintype A] [Fintype J] [Fintype H]
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (hI : ∀ p ∈ I, 0 < p)
    (φ : ℝ → ℝ) (G : ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass P φ G)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμmass : ∑ y, μ y = 1)
    (U : Y → ℕ) (hU : ∀ y, 0 < U y)
    (Q : Y → P → J → ℕ) [∀ y p j, Fact (Q y p j).Prime]
    (gQ : ∀ y p j, ZMod (Q y p j) → ℂ)
    (hQprod : ∀ y p, (∏ j, Q y p j) = (p : ℕ) * U y)
    (giant : J) (S : ∀ y p j, Finset (ZMod (Q y p j)))
    (hgQ : ∀ y p x, ‖gQ y p giant x‖ ≤ 1)
    (hregular : ∀ y p j, j ≠ giant → gQ y p j = normalizedResidueTransform (S y p j))
    (hS : ∀ y p j, j ≠ giant → (S y p j).Nonempty)
    (hSp : ∀ y p j, j ≠ giant → (S y p j).card < Q y p j)
    (L : Y → A → H → ℕ) [∀ y a i, Fact (L y a i).Prime]
    (gL : ∀ y a i, ZMod (L y a i) → ℂ)
    (hgL : ∀ y a i x, gL y a i (-x) = conj (gL y a i x))
    (D : Y → ℕ) (v : Y → A → ℤ) (W : Y → ℕ → A → ℂ)
    (hrowSupport : ∀ y (p : P) a, W y p a ≠ 0 →
      Pairwise (fun i j => (Q y p i).Coprime (Q y p j)) ∧
      ∀ j, (D y).Coprime (Q y p j))
    (hsupport : ∀ y p, p ∈ I → ∀ a, W y p a ≠ 0 →
      Pairwise (fun i j => (L y a i).Coprime (L y a j)) ∧
      (∏ i, L y a i).Coprime (p * U y) ∧ ∀ i, (D y).Coprime (L y a i))
    (N B V : ℕ)
    (hv : ∀ y p, p ∈ I → ∀ a, W y p a ≠ 0 → (v y a).natAbs ≤ N)
    (hL : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → ∀ a, W y p a ≠ 0 → (∏ i, L y a i) ≤ B)
    (hscale : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → 2 * N * B ≤ V * (p * U y))
    (hlarge : ∀ y p, p ∈ I → ∀ a, W y p a ≠ 0 →
      ∀ q, q.Prime → q ∣ ∏ i, L y a i → V < q) :
    Real.exp (-smoothGiantLogNormalizer P φ G) *
      ‖∑ y, (μ y : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
        ∑ a, W y p a * movingRegularTransform (Sum.elim (Q y p) (L y a))
          (movingSumFactors (Q y p) (L y a) (gQ y p) (gL y a)) (D y) (v y a)‖ ^ 2 ≤
      (∑ y, μ y * (U y : ℝ) * ∑ p ∈ I, φ (Real.log p - G) *
        (pivotDiagonal (fun a => ∏ i, L y a i) (v y)
          (movingRegularCoefficient (L y) (gL y) (D y) (U y) (v y) (W y) p)).re) +
      ‖∑ y, ((μ y * (U y : ℝ) : ℝ) : ℂ) *
        ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
          if validTransferredPivot I
              (v y a * (∏ i, L y b i) - v y b * (∏ i, L y a i)) (s * U y) then
            let p := reconstructedPivot
              (v y a * (∏ i, L y b i) - v y b * (∏ i, L y a i)) (s * U y)
            (φ (Real.log p - G) : ℂ) * W y p a * conj (W y p b) *
              movingRegularTransform (Sum.elim (L y a) (L y b))
                (movingSumFactors (L y a) (L y b) (gL y a) (gL y b)) (D y) s
          else 0‖ := by
  let c := fun y => movingRegularCoefficient (L y) (gL y) (D y) (U y) (v y) (W y)
  have hc (y : Y) (p : ℕ) (a : A) (h : c y p a ≠ 0) : W y p a ≠ 0 := by
    intro hz
    apply h
    simp only [c, movingRegularCoefficient, hz, zero_mul]
  have ht := smoothGiantPrior_transfer_on_prior P I hP hPI hI φ G hφ hpos μ hμ hμmass U hU
    (fun y p => movingGuardedRow (Q y p) (gQ y p) (D y))
    (fun y p => by
      simpa only [Nat.cast_mul] using
        movingGuardedRow_energy (Q y p) (gQ y p) (D y) ((p : ℕ) * U y)
          (hQprod y p) giant (S y p) (hgQ y p) (hregular y p) (hS y p) (hSp y p))
    (fun y a => ∏ i, L y a i) v c
    (fun y p hp a h => (hsupport y p hp a (hc y p a h)).2.1) N B V
    (fun y p hp a h => hv y p hp a (hc y p a h))
    (fun y hy p hp a h => hL y hy p hp a (hc y p a h)) hscale
  have hsum : (∑ y, (μ y : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
      ∑ a, movingGuardedRow (Q y p) (gQ y p) (D y)
        (positiveIntegerPivotKey ((p : ℕ) * U y)
          (Nat.mul_pos (hP p p.property).pos (hU y)) (∏ i, L y a i) (v y a)) * c y p a) =
      ∑ y, (μ y : ℂ) * ∑ p : P, (smoothGiantPrior P φ G p : ℂ) *
        ∑ a, W y p a * movingRegularTransform (Sum.elim (Q y p) (L y a))
          (movingSumFactors (Q y p) (L y a) (gQ y p) (gL y a)) (D y) (v y a) := by
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases hz : W y p a = 0
    · simp only [c, movingRegularCoefficient, hz, zero_mul, mul_zero]
    · have hs := hrowSupport y p a hz
      rw [moving_full_transform_guarded (Q y p) (L y a) (gQ y p) (gL y a)
        (D y) ((p : ℕ) * U y) (hQprod y p)
        (Nat.mul_pos (hP p p.property).pos (hU y)) (v y a) hs.1 hs.2
        (hsupport y p (hPI p.property) a hz).2.1]
      dsimp only [c, movingRegularCoefficient]
      ring
  rw [hsum] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  dsimp only [c]
  rw [movingGiantOffDiagonal_regular_on_live (L y) (gL y) (hgL y) I V (U y) (D y)
    (v y) (fun p => φ (Real.log p - G)) (W y) (hsupport y) (hlarge y)]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · congr 1
    congr 1
    funext i
    cases i <;> rfl
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLiveRaw
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One giant-prior step with a product bound only on actual coefficient support -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.liveTemplateSum_neZero
/-- The support fields in the full Fourier transfer follow from the
original coefficient. Compensation retains its original independent law;
`α` contains the surviving external priors. -/
theorem movingTemplate_prior_transfer_raw_on_live {σ A : Type} [Fintype σ] [Fintype A]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass P φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (X : A → ℕ) (hX : ∀ a, (X a).Prime)
    (y : A → MovingRegularSlot n r m → σ) (v : A → ℤ) (α : A → ℂ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ a x, ggiant (X a) (-x) = conj (ggiant (X a) x))
    (N H T : ℕ) (hv : ∀ a, (v a).natAbs ≤ N)
    (hH : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ), p ∈ I → ∀ a,
      movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G
        n r m v α X y u p a ≠ 0 → X a * (∏ i, value (y a i)) ≤ H)
    (hscale : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 → ∀ p, p ∈ I →
      2 * N * H ≤ T * (p * ∏ i, value (u i)))
    (hlarge : ∀ a, α a ≠ 0 → ∀ q, q.Prime →
      q ∣ X a * (∏ i, value (y a i)) → T < q) :
    let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
    let _ : ∀ a i, Fact (((value ∘ y a) i)).Prime := fun a i => ⟨hvalue (y a i)⟩
    let greg := normalizedResidueFamily sets
    let U := fun u : TreeLeafIndex n × Fin 4 → σ => ∏ i, value (u i)
    let L := fun a => movingOneGiantModuli (X a) (value ∘ y a)
    let _ : ∀ a i, NeZero (L a i) := fun a i => by
      cases i with
      | inl _ => exact ⟨(hX a).ne_zero⟩
      | inr j => exact ⟨(hvalue (y a j)).ne_zero⟩
    let gL := fun a => movingOneGiantFactors (X a) (value ∘ y a) greg ggiant favorable
    let Q := fun (u : TreeLeafIndex n × Fin 4 → σ) (p : P) =>
      movingOneGiantModuli (p : ℕ) (value ∘ u)
    let _ : ∀ u p i, NeZero (Q u p i) := fun u p i => by
      cases i with
      | inl _ => exact ⟨(hP p p.property).ne_zero⟩
      | inr j => exact ⟨(hvalue (u j)).ne_zero⟩
    let gQ := fun (u : TreeLeafIndex n × Fin 4 → σ) (p : P) =>
      movingOneGiantFactors (p : ℕ) (value ∘ u) greg ggiant favorable
    let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m v α X y
    Real.exp (-smoothGiantLogNormalizer P φ (G (n + 1))) *
      ‖∑ u : TreeLeafIndex n × Fin 4 → σ, ((∏ i, μ n (u i) : ℝ) : ℂ) *
        ∑ p : P, (smoothGiantPrior P φ (G (n + 1)) p : ℂ) *
          ∑ a, W u p a * movingRegularTransform (Sum.elim (Q u p) (L a))
            (movingSumFactors (Q u p) (L a) (gQ u p) (gL a)) outside.prod (v a)‖ ^ 2 ≤
      (∑ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) * (U u : ℝ) *
        ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
          (pivotDiagonal (fun a => ∏ i, L a i) v
            (movingRegularCoefficient L gL outside.prod (U u) v (W u) p)).re) +
      ‖∑ u : TreeLeafIndex n × Fin 4 → σ, (((∏ i, μ n (u i)) * (U u : ℝ) : ℝ) : ℂ) *
        ∑ s ∈ transferFrequencyRange T, ∑ a, ∑ b,
          if validTransferredPivot I
              (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U u) then
            let p := reconstructedPivot
              (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U u)
            (φ (Real.log p - G (n + 1)) : ℂ) * W u p a * conj (W u p b) *
              movingRegularTransform (Sum.elim (L a) (L b))
                (movingSumFactors (L a) (L b) (gL a) (gL b)) outside.prod s
          else 0‖ := by
  let : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
  let : ∀ a, Fact (value a).Prime := fun a => ⟨hvalue a⟩
  let : ∀ a i, Fact (((value ∘ y a) i)).Prime := fun a i => ⟨hvalue (y a i)⟩
  let greg := normalizedResidueFamily sets
  let U := fun u : TreeLeafIndex n × Fin 4 → σ => ∏ i, value (u i)
  let Q := fun (u : TreeLeafIndex n × Fin 4 → σ) (p : P) =>
    movingOneGiantModuli (p : ℕ) (value ∘ u)
  let L := fun a => movingOneGiantModuli (X a) (value ∘ y a)
  let : ∀ (u : TreeLeafIndex n × Fin 4 → σ) (p : P) i, Fact (Q u p i).Prime := by
    intro u p i
    cases i with
    | inl _ => exact ⟨hP p p.property⟩
    | inr j => exact ⟨hvalue (u j)⟩
  let gQ := fun (u : TreeLeafIndex n × Fin 4 → σ) (p : P) =>
    movingOneGiantFactors (p : ℕ) (value ∘ u) greg ggiant favorable
  let : ∀ a i, Fact (L a i).Prime := fun a i => by
    cases i <;> dsimp only [L, movingOneGiantModuli, Sum.elim, Function.comp_apply] <;> infer_instance
  let : ∀ a i, NeZero (L a i) := fun a i => by infer_instance
  let gL := fun a => movingOneGiantFactors (X a) (value ∘ y a) greg ggiant favorable
  let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m v α X y
  have hprod (a : A) : (∏ i, L a i) = X a * ∏ i, value (y a i) :=
    movingOneGiantModuli_product (X a) (value ∘ y a)
  have hQprod u p : (∏ i, Q u p i) = (p : ℕ) * U u :=
    movingOneGiantModuli_product (p : ℕ) (value ∘ u)
  have hs u p a (h : W u p a ≠ 0) :=
    movingTemplateTransferWeight_support value outside μ childBound pivotBound V F φ G
      n r m v α X y u p a h
  have hgL a i x : gL a i (-x) = conj (gL a i x) :=
    movingOneGiantFactors_neg (X a) (value ∘ y a) greg ggiant favorable
      (hgiant a) (fun j x => by
        dsimp only [greg]
        rw [normalizedResidueFamily_eq]
        exact normalizedResidueTransform_neg _ x) i x
  have ht := smoothGiantPrior_full_transform_transfer_on_live
    (Y := TreeLeafIndex n × Fin 4 → σ) (A := A)
    (J := Unit ⊕ (TreeLeafIndex n × Fin 4)) (H := Unit ⊕ MovingRegularSlot n r m) P I hP hPI hI φ (G (n + 1)) hφ hpos
    (fun u : TreeLeafIndex n × Fin 4 → σ => ∏ i, μ n (u i))
    (fun u => Finset.prod_nonneg (fun i _ => hμ (u i)))
    (by rw [← Fintype.prod_sum]; simp only [hμmass, Finset.prod_const_one]) U
    (fun u => Finset.prod_pos (fun i _ => (hvalue (u i)).pos)) Q gQ hQprod (.inl ())
    (fun u p i => match i with | .inl _ => ∅ | .inr j => sets (value (u j)))
    (fun u p x => by
      change ‖if favorable (p : ℕ) then complexUnitPhase (ggiant p x) else 0‖ ≤ 1
      split_ifs
      · exact complexUnitPhase_norm_le _
      · simp)
    (fun u p i hi => by
      cases i with
      | inl i => cases i; exact (hi rfl).elim
      | inr j => exact normalizedResidueFamily_eq sets (value (u j)))
    (fun u p i hi => by
      cases i with
      | inl i => cases i; exact (hi rfl).elim
      | inr j => exact hsets (u j))
    (fun u p i hi => by
      cases i with
      | inl i => cases i; exact (hi rfl).elim
      | inr j => exact hcard (u j)) (fun _ => L) (fun _ => gL) (fun _ => hgL) (fun _ => outside.prod) (fun _ => v) W
    (fun u p a hw => ⟨(hs u p a hw).1, (hs u p a hw).2.1⟩)
    (fun u p _ a hw => by
      have h := hs u p a hw
      refine ⟨h.2.2.1, ?_, h.2.2.2.2⟩
      have hc := h.2.2.2.1
      change (∏ i, L a i).Coprime (∏ i, movingOneGiantModuli p (value ∘ u) i) at hc
      simpa only [L, U, movingOneGiantModuli_product, Function.comp_apply] using hc)
    N H T (fun _ _ _ a _ => hv a) (fun u hu p hp a ha => (hprod a).trans_le (hH u hu p hp a ha))
    hscale (fun _ _ _ a hw q hq hd =>
      hlarge a (left_ne_zero_of_mul hw) q hq ((hprod a) ▸ hd))
  with_reducible exact ht

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLiveTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full giant-prior step with its actual supported product bound -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.liveFinalSum_neZero
/-- The support fields in the full Fourier transfer follow from the
original coefficient. Compensation retains its original independent law;
`α` contains the surviving external priors. -/
theorem movingTemplate_prior_transfer_on_live {σ A : Type} [Fintype σ] [Fintype A]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass P φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (X : A → ℕ) (hX : ∀ a, (X a).Prime)
    (y : A → MovingRegularSlot n r m → σ) (v : A → ℤ) (α : A → ℂ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ a x, ggiant (X a) (-x) = conj (ggiant (X a) x))
    (N H T : ℕ) (hv : ∀ a, (v a).natAbs ≤ N)
    (hH : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ), p ∈ I → ∀ a,
      movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G
        n r m v α X y u p a ≠ 0 → X a * (∏ i, value (y a i)) ≤ H)
    (hscale : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 → ∀ p, p ∈ I →
      2 * N * H ≤ T * (p * ∏ i, value (u i)))
    (hlarge : ∀ a, α a ≠ 0 → ∀ q, q.Prime →
      q ∣ X a * (∏ i, value (y a i)) → T < q) :
    let _ : ∀ a, Fact (X a).Prime := fun a => ⟨hX a⟩
    let _ : ∀ a i, Fact (((value ∘ y a) i)).Prime := fun a i => ⟨hvalue (y a i)⟩
    let greg := normalizedResidueFamily sets
    let U := fun u : TreeLeafIndex n × Fin 4 → σ => ∏ i, value (u i)
    let L := fun a => movingOneGiantModuli (X a) (value ∘ y a)
    let _ : ∀ a i, NeZero (L a i) := fun a i => by
      cases i with
      | inl _ => exact ⟨(hX a).ne_zero⟩
      | inr j => exact ⟨(hvalue (y a j)).ne_zero⟩
    let gL := fun a => movingOneGiantFactors (X a) (value ∘ y a) greg ggiant favorable
    let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m v α X y
    Real.exp (-smoothGiantLogNormalizer P φ (G (n + 1))) *
      ‖∑ u : TreeLeafIndex n × Fin 4 → σ, ((∏ i, μ n (u i) : ℝ) : ℂ) *
        ∑ p : P, (smoothGiantPrior P φ (G (n + 1)) p : ℂ) *
          ∑ a, W u p a * movingTaggedTransform
            (Sum.elim (fun b : Bool => if b then (p : ℕ) else X a)
              (value ∘ movingRestoreSample n r m u (y a)))
            (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod (v a)‖ ^ 2 ≤
      (∑ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) * (U u : ℝ) *
        ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
          (pivotDiagonal (fun a => ∏ i, L a i) v
            (movingRegularCoefficient L gL outside.prod (U u) v (W u) p)).re) +
      ‖∑ u : TreeLeafIndex n × Fin 4 → σ, (((∏ i, μ n (u i)) * (U u : ℝ) : ℝ) : ℂ) *
        ∑ s ∈ transferFrequencyRange T, ∑ a, ∑ b,
          if validTransferredPivot I
              (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U u) then
            let p := reconstructedPivot
              (v a * (∏ i, L b i) - v b * (∏ i, L a i)) (s * U u)
            (φ (Real.log p - G (n + 1)) : ℂ) * W u p a * conj (W u p b) *
              movingRegularTransform (Sum.elim (L a) (L b))
                (movingSumFactors (L a) (L b) (gL a) (gL b)) outside.prod s
          else 0‖ := by
  let greg := normalizedResidueFamily sets
  let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G n r m v α X y
  have ht := movingTemplate_prior_transfer_raw_on_live value hvalue outside μ childBound pivotBound V F
    φ G n r m P I hP hPI hI hφ hpos hμ hμmass X hX y v α sets hsets hcard ggiant favorable
    hgiant N H T hv hH hscale hlarge
  have hsum := movingOneGiant_restored_average value (fun z => (hvalue z).ne_zero) n r m
    P (fun p => (hP p p.property).ne_zero) X (fun a => (hX a).ne_zero) y v outside.prod
    greg ggiant favorable (fun u => ((∏ i, μ n (u i) : ℝ) : ℂ))
    (fun p => (smoothGiantPrior P φ (G (n + 1)) p : ℂ)) (fun u p a => W u p a)
  exact (congrArg (fun z : ℂ =>
    Real.exp (-smoothGiantLogNormalizer P φ (G (n + 1))) * ‖z‖ ^ 2) hsum).le.trans ht

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeLiveTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer of the original amplitude with its supported product window -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Specialization to the actual surviving giant, regular tuple and frequency.
The compensation draw and the giant harmonic normalization are unchanged. -/
theorem movingTemplatePrimeAmplitude_transfer_on_live {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : Pg ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : Pg, ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hH : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ), p ∈ I →
      ∀ (q : Pg) (y : MovingRegularSlot n r m → σ) (s : transferFrequencyRange (V n)),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
        n (4 + r) m s.val (movingRestoreSample n r m u y) p q ≠ 0 →
        (q : ℕ) * (∏ i, value (y i)) ≤ H)
    (hscale : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 → ∀ p ∈ I,
      2 * V n * H ≤ V (n + 1) * (p * ∏ i, value (u i)))
    (hlarge : ∀ (q : Pg) (y : MovingRegularSlot n r m → σ),
      (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingAmplitudeOffDiagonal value outside μ childBound pivotBound V F φ G n r m Pg I
        ρ ν greg ggiant favorable‖ := by
  intro ρ greg
  let A := MovingAmplitudeIndex σ Pg n r m V
  let X := fun a : A => (a.1 : ℕ)
  let y := fun a : A => a.2.1
  let v := fun a : A => a.2.2.val
  let α := fun a : A => (movingAmplitudePrior Pg n r m V ρ ν a : ℂ)
  let : ∀ a : A, Fact (X a).Prime := fun a => ⟨hPg _ a.1.property⟩
  let : ∀ a : A, ∀ i, Fact (value (y a i)).Prime := fun a i => ⟨hvalue (y a i)⟩
  let : ∀ a : A, ∀ i, NeZero ((value ∘ y a) i) :=
    fun a i => ⟨(hvalue (y a i)).ne_zero⟩
  let L := fun a => movingOneGiantModuli (X a) (value ∘ y a)
  let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G
    n r m v α X y
  have ht := movingTemplate_prior_transfer_on_live value hvalue outside μ childBound pivotBound V F
    φ G n r m Pg I hPg hPI hI hφ hpos hμ hμmass X (fun a => hPg _ a.1.property)
    y v α sets hsets hcard ggiant favorable (fun a => hgiant a.1)
    (V n) H (V (n + 1)) (fun a => (mem_transferFrequencyRange _ _).mp a.2.2.property)
    (fun u hu p hp a ha => hH u hu p hp a.1 (y a) a.2.2 (right_ne_zero_of_mul ha)) hscale (fun a ha => by
      have hprior : movingAmplitudePrior Pg n r m V ρ ν a ≠ 0 :=
        Complex.ofReal_ne_zero.mp ha
      exact hlarge a.1 (y a) (right_ne_zero_of_mul hprior))
  dsimp only at ht
  rw [← movingTemplatePrimeAmplitude_index] at ht
  have hC u p : movingRegularCoefficient L
      (fun a => movingOneGiantFactors (X a) (value ∘ y a) greg ggiant favorable)
      outside.prod (∏ i, value (u i)) v (W u) p =
      fun a => W u p a * movingTaggedTransform (L a)
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable
        (p * (∏ i, value (u i)) * outside.prod) (v a) := by
    funext a
    exact congrArg (fun z => W u p a * z)
      (movingOneGiant_transform_tagged (X a) (value ∘ y a) greg ggiant favorable
        (p * (∏ i, value (u i)) * outside.prod) (v a))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  · unfold movingAmplitudeDiagonal
    apply Finset.sum_congr rfl
    intro u _
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    simp only [movingOneGiantModuli_product, Function.comp_apply]
    exact congrArg (fun c : A → ℂ =>
      (pivotDiagonal (fun a => X a * ∏ i, value (y a i)) v c).re) (hC u p).symm
  · congr 1
    unfold movingAmplitudeOffDiagonal
    apply Finset.sum_congr rfl
    intro u _
    congr 1
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [movingOneGiantModuli_product, Function.comp_apply,
      movingOneGiant_pair_transform_tagged]
    dsimp only [movingTemplateIntegerFourierTerm, movingTemplateTransferWeight, A, X, y, v, α, W]
    split_ifs
    · simp only [map_mul, Complex.conj_ofReal]
      simp only [starRingEnd_apply]
      dsimp only [greg]
      ring
    · simp only [mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalLeafMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar multipliers in the original terminal coefficient -/

namespace Ostmann
open scoped Classical SchwartzMap

theorem movingOriginalLeaf_zero {σ I : Type*} (value : σ → ℕ) (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) :
    movingOriginalLeaf value q F g Dq S ψ X lo hi x 0 = 0 := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  split <;> simp only [hF, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingNodeCoefficientSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer substitution on the nonzero original coefficient support -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingPrimeNodeFactor_substitution_on_right {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (u : TreeLeafTuple (List σ) n) (small bulk : TreeLeafTuple (List σ) (n + 1))
    (XL XR : ℕ) (s v w : ℤ) (I : Finset ℕ)
    (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hsV : s.natAbs ≤ V (n + 1))
    (hv : v.natAbs ≤ childBound (n + 1)) (hw : w.natAbs ≤ childBound (n + 1)) :
    let U := MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let LH := XL * MovingSlotReversal.naturalProduct value CL
    let RH := XR * MovingSlotReversal.naturalProduct value CR
    let p := movingTopPivot value CL CR (flattenMovingSlots n u) XL XR s v w
    let A := movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n v
      (appendMovingSlotLeaves n u small.1) bulk.1 p XL
    let B := movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n w
      (appendMovingSlotLeaves n u small.2) bulk.2 p XR
    (∀ p ∈ I, p * U ≤ pivotBound (n + 1)) →
    (B ≠ 0 → 2 * pivotBound (n + 1) * childBound (n + 1) < RH) →
    (∀ q, q.Prime → q ∣ RH → V (n + 1) < q) →
    (∀ q, q.Prime → q ∣ U → childBound (n + 1) < q) →
    movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
      (flattenMovingSlots n u) XL XR s v w * A * star B =
      if validTransferredPivot I (v * RH - w * LH) (s * U) then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) * A * star B else 0  := by
  intro U CL CR LH RH p A B hbound hgap hRH hU
  by_cases hB : B = 0
  · simp only [hB, star_zero, mul_zero, ite_self]
  · exact movingPrimeNodeFactor_substitution value outside μ childBound pivotBound V F hF
      φ G n u small bulk XL XR s v w I hI hφ hsV hv hw hbound (hgap hB) hRH hU

theorem movingTemplateCoefficient_integer_node_on_coefficients {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (hsV : s.natAbs ≤ V (n + 1))
    (left right : MovingRegularSlot n r m → σ) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR)
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < XR * ∏ i, value (right i))
    (hRH : ∀ q, q.Prime → q ∣ XR * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s
      (movingTemplatePairSample n r m left right) XL XR =
    ∑ u : TreeLeafIndex n × Fin 4 → σ,
      (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
      ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
        let LH := XL * ∏ i, value (left i)
        let RH := XR * ∏ i, value (right i)
        let p := reconstructedPivot (v.val * RH - w.val * LH) (s * ∏ i, value (u i))
        if validTransferredPivot I (v.val * RH - w.val * LH) (s * ∏ i, value (u i)) then
          (φ (Real.log p - G (n + 1)) : ℂ) *
            movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m v.val
              (movingRestoreSample n r m u left) p XL *
            star (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w.val
              (movingRestoreSample n r m u right) p XR)
        else 0 := by
  by_cases hs : s = 0
  · subst s
    change movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      (n + 1) 0 _ _ XL XR = _
    rw [movingFrequencyCoefficient_zero value outside μ childBound pivotBound V F hF φ G]
    simp only [zero_mul, validTransferredPivot, ne_eq, not_true_eq_false, false_and,
      ite_false, if_false, Finset.sum_const_zero, mul_zero]
  ·
    let K := fun u : TreeLeafIndex n × Fin 4 → σ =>
      (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
        ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
          let LH := XL * ∏ i, value (left i)
          let RH := XR * ∏ i, value (right i)
          let p := reconstructedPivot (v.val * RH - w.val * LH) (s * ∏ i, value (u i))
          if validTransferredPivot I (v.val * RH - w.val * LH) (s * ∏ i, value (u i)) then
            (φ (Real.log p - G (n + 1)) : ℂ) *
              movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m v.val
                (movingRestoreSample n r m u left) p XL *
              star (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w.val
                (movingRestoreSample n r m u right) p XR)
          else 0
    change _ = ∑ u, K u
    rw [← (movingTemplateCompensationEquiv σ n).sum_comp K]
    rw [movingTemplateCoefficient_prime_node value outside μ childBound pivotBound V hV F hF
      φ G n r m s hs hsV left right XL XR hXL hXR hVL hVR]
    apply Finset.sum_congr rfl
    intro a _
    have hpμ := movingTemplateCompensationEquiv_prior (μ n) n a
    have hU := movingTemplateCompensationEquiv_product value n a
    by_cases ha : movingCompensationPrior (μ n) n a = 0
    · simp only [K, hpμ, ha, Complex.ofReal_zero, zero_mul]
    · have hc := hcomp (movingTemplateCompensationEquiv σ n a) (hpμ ▸ ha)
      dsimp only [K]
      rw [hpμ, Complex.ofReal_mul, mul_assoc]
      apply congrArg (fun z : ℂ => (movingCompensationPrior (μ n) n a : ℂ) * z)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      let small := (treeLeafMap (List.map left) n (movingTemplateSmall n r m),
        treeLeafMap (List.map right) n (movingTemplateSmall n r m))
      let bulk := (treeLeafMap (List.map left) n (bulkSlotLeaves n m (movingTemplateBulk n r m)),
        treeLeafMap (List.map right) n (bulkSlotLeaves n m (movingTemplateBulk n r m)))
      have ht := movingPrimeNodeFactor_substitution_on_right value outside μ childBound pivotBound V F hF
        φ G n (movingCompensationSlots n a) small bulk XL XR s v.val w.val I hI hφ hsV
        (((mem_transferFrequencyRange _ _).mp v.property).trans hchild)
        (((mem_transferFrequencyRange _ _).mp w.property).trans hchild)
      dsimp only [small, bulk] at ht
      have hCL := movingTemplateMapped_product value n r m left
      have hCR := movingTemplateMapped_product value n r m right
      simp only [hU, hCL, hCR] at ht
      specialize ht hc.1 (fun hB => hgap (movingTemplateCompensationEquiv σ n a)
        (hpμ ▸ ha) _ _ (by simpa only [movingTemplateCoefficient_restored] using hB)) hRH hc.2
      simp only [movingTemplateCoefficient_restored]
      dsimp only [movingTopPivot] at ht ⊢
      simp only [hU, hCL, hCR, Complex.ofReal_mul, Nat.cast_prod] at ht ⊢
      split_ifs at ht ⊢ <;> simpa only [mul_assoc, mul_zero] using ht

theorem movingTemplateCoefficient_transformed_integer_node_on_coefficients {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (hsV : s.natAbs ≤ V (n + 1))
    (left right : MovingRegularSlot n r m → σ) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR)
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < XR * ∏ i, value (right i))
    (hRH : ∀ q, q.Prime → q ∣ XR * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (hleft : ∀ i, value (left i) ≠ 0) (hright : ∀ i, value (right i) ≠ 0)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s
      (movingTemplatePairSample n r m left right) XL XR *
      movingTaggedTransform
        (Sum.elim (fun b : Bool => if b then XL else XR)
          (value ∘ movingTemplatePairSample n r m left right))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s =
    ∑ u : TreeLeafIndex n × Fin 4 → σ,
      (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
      ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
        let LH := XL * ∏ i, value (left i)
        let RH := XR * ∏ i, value (right i)
        let p := reconstructedPivot (v.val * RH - w.val * LH) (s * ∏ i, value (u i))
        if validTransferredPivot I (v.val * RH - w.val * LH) (s * ∏ i, value (u i)) then
          (φ (Real.log p - G (n + 1)) : ℂ) *
            movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m v.val
              (movingRestoreSample n r m u left) p XL *
            star (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w.val
              (movingRestoreSample n r m u right) p XR) *
            movingTaggedTransform
              (Sum.elim (movingOneGiantModuli XL (value ∘ left))
                (movingOneGiantModuli XR (value ∘ right)))
              (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
                (Sum.elim (fun _ : Unit => true) (fun _ => false)))
              greg ggiant favorable outside.prod s
        else 0 := by
  have hn := movingTemplateCoefficient_integer_node_on_coefficients value outside μ childBound pivotBound V hV
    F hF φ G n r m s hsV left right XL XR hXL hXR hVL hVR I hI hφ hchild hgap hRH hcomp
  have ht := movingTaggedTransform_paired value n r m left right XL XR
    hXL.ne_zero hXR.ne_zero hleft hright greg ggiant favorable outside.prod s
  rw [hn, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_assoc, Finset.sum_mul]
  apply congrArg (fun z : ℂ =>
    (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) * z)
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  dsimp only
  split_ifs
  · congr 1
    exact ht.symm
  · exact zero_mul _

theorem movingTemplateCoefficient_averaged_integer_node_on_coefficients {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (hsV : s.natAbs ≤ V (n + 1))
    (ν : MovingRegularSlot (n + 1) r m → σ → ℝ)
    (XL XR : ℕ) (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR)
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < XR * ∏ i, value (right i))
    (hRH : ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      ∀ q, q.Prime → q ∣ XR * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    (∑ y : MovingRegularSlot (n + 1) r m → σ, ((∏ i, ν i (y i) : ℝ) : ℂ) *
      (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s y XL XR *
        movingTaggedTransform
          (Sum.elim (fun b : Bool => if b then XL else XR) (value ∘ y))
          (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s)) =
    ∑ u : TreeLeafIndex n × Fin 4 → σ,
      (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
      ∑ left : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν true left : ℂ) *
        ∑ right : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν false right : ℂ) *
          ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
            movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G n r m I
              XL XR s left right greg ggiant favorable u v.val w.val := by
  let A := fun y : MovingRegularSlot (n + 1) r m → σ =>
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s y XL XR *
      movingTaggedTransform
        (Sum.elim (fun b : Bool => if b then XL else XR) (value ∘ y))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s
  let M := fun u : TreeLeafIndex n × Fin 4 → σ =>
    (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ)
  let B := fun left right u =>
    ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
      movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G n r m I
        XL XR s left right greg ggiant favorable u v.val w.val
  have hn left right (hr : movingTemplateSidePrior n r m ν false right ≠ 0) :
      A (movingTemplatePairSample n r m left right) = ∑ u, M u * B left right u := by
    exact movingTemplateCoefficient_transformed_integer_node_on_coefficients value outside μ childBound pivotBound V hV
      F hF φ G n r m s hsV left right XL XR hXL hXR hVL hVR I hI hφ hchild
      (hgap right hr) (hRH right hr) hcomp (fun i => (hvalue _).ne_zero)
      (fun i => (hvalue _).ne_zero) greg ggiant favorable
  change (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * A y) = _
  rw [movingTemplatePair_average]
  change (∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
    ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) *
      A (movingTemplatePairSample n r m left right)) = _
  have he : (∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
      ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) *
        A (movingTemplatePairSample n r m left right)) =
      ∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
        ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) *
          ∑ u, M u * B left right u := by
    apply Finset.sum_congr rfl
    intro left _
    congr 1
    apply Finset.sum_congr rfl
    intro right _
    by_cases hr : movingTemplateSidePrior n r m ν false right = 0
    · simp only [hr, Complex.ofReal_zero, zero_mul]
    · rw [hn left right hr]
  rw [he]
  change _ = ∑ u, M u * ∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
    ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) * B left right u
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext left
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

theorem movingTemplatePrimeAmplitude_next_on_coefficients {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (hPg : ∀ q ∈ Pg, q.Prime) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot (n + 1) r m → σ → ℝ)
    (hlarge : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hRH : ∀ XR : Pg, ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      ∀ q, q.Prime → q ∣ (XR : ℕ) * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
      Pg ρ ν greg ggiant favorable =
    ∑ XL : Pg, (ρ XL : ℂ) * ∑ XR : Pg, (ρ XR : ℂ) *
      ∑ s : transferFrequencyRange (V (n + 1)),
        ∑ u : TreeLeafIndex n × Fin 4 → σ,
          (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
            ∑ left : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν true left : ℂ) *
              ∑ right : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν false right : ℂ) *
                ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
                  movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G
                    n r m I XL XR s.val left right greg ggiant favorable u v.val w.val := by
  unfold movingTemplatePrimeAmplitude
  apply Finset.sum_congr rfl
  intro XL _
  congr 1
  apply Finset.sum_congr rfl
  intro XR _
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact movingTemplateCoefficient_averaged_integer_node_on_coefficients value hvalue outside μ
    childBound pivotBound V hV F hF φ G n r m s.val
    ((mem_transferFrequencyRange _ _).mp s.property) ν XL XR
    (hPg _ XL.property) (hPg _ XR.property) (hlarge XL) (hlarge XR)
    I hI hφ hchild (hgap XR) (hRH XR) hcomp greg ggiant favorable

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeCoefficientSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full moving transfer with separation on its actual coefficient support -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

private theorem coefficient_amplitude_pair_sum {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (ρ : A → ℝ) (ν : B → ℝ) (F : A → A → B → B → C → C → ℂ) :
    (∑ a : A × (B × C), ∑ b : A × (B × C),
      ((ρ a.1 * ν a.2.1 : ℝ) : ℂ) * ((ρ b.1 * ν b.2.1 : ℝ) : ℂ) *
        F a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2) =
      ∑ x, (ρ x : ℂ) * ∑ z, (ρ z : ℂ) *
        ∑ y, (ν y : ℂ) * ∑ t, (ν t : ℂ) * ∑ v, ∑ w, F x z y t v w := by
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Complex.ofReal_mul]
  conv_lhs =>
    arg 2
    ext x
    arg 2
    ext y
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    arg 2
    ext z
    arg 2
    ext y
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

private theorem coefficient_amplitude_full_sum {U S A B C : Type}
    [Fintype U] [Fintype S] [Fintype A] [Fintype B] [Fintype C]
    (M : U → ℂ) (ρ : A → ℝ) (ν : B → ℝ)
    (F : U → S → A → A → B → B → C → C → ℂ) :
    (∑ u, M u * ∑ s, ∑ a : A × (B × C), ∑ b : A × (B × C),
      ((ρ a.1 * ν a.2.1 : ℝ) : ℂ) * ((ρ b.1 * ν b.2.1 : ℝ) : ℂ) *
        F u s a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2) =
    ∑ XL, (ρ XL : ℂ) * ∑ XR, (ρ XR : ℂ) * ∑ s, ∑ u, M u *
      ∑ left, (ν left : ℂ) * ∑ right, (ν right : ℂ) * ∑ v, ∑ w,
        F u s XL XR left right v w := by
  simp_rw [coefficient_amplitude_pair_sum]
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro XL _
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro XR _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem movingAmplitudeOffDiagonal_eq_next_on_coefficients {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (hPg : ∀ q ∈ Pg, q.Prime) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (hlarge : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hRH : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ q, q.Prime → q ∣ (XR : ℕ) * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingAmplitudeOffDiagonal value outside μ childBound pivotBound V F φ G n r m Pg I
      ρ ν greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
      Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable := by
  rw [movingTemplatePrimeAmplitude_next_on_coefficients value hvalue outside μ childBound pivotBound V hV
    F hF φ G n r m Pg hPg ρ (movingTemplateDoubledPrior n r m ν) hlarge I hI hφ hchild
    (by simpa only [movingTemplateDoubledPrior_side] using hgap)
    (by simpa only [movingTemplateDoubledPrior_side] using hRH) hcomp]
  simp only [movingTemplateDoubledPrior_side]
  unfold movingAmplitudeOffDiagonal
  dsimp only [movingAmplitudePrior]
  have hr := coefficient_amplitude_full_sum
    (U := TreeLeafIndex n × Fin 4 → σ) (S := transferFrequencyRange (V (n + 1)))
    (A := Pg) (B := MovingRegularSlot n r m → σ) (C := transferFrequencyRange (V n))
    (fun u => (((∏ i, μ n (u i)) * (∏ i, value (u i) : ℕ) : ℝ) : ℂ))
    ρ (fun y => ∏ i, ν i (y i))
    (fun u s XL XR left right v w => movingTemplateIntegerFourierTerm value outside μ
      childBound pivotBound V F φ G n r m I XL XR s.val left right greg ggiant favorable
        u v.val w.val)
  convert hr using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.cast_prod]

theorem movingTemplatePrimeAmplitude_step_on_coefficients {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : Pg ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : Pg, ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hH : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ), p ∈ I →
      ∀ (q : Pg) (y : MovingRegularSlot n r m → σ) (s : transferFrequencyRange (V n)),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
        n (4 + r) m s.val (movingRestoreSample n r m u y) p q ≠ 0 →
        (q : ℕ) * (∏ i, value (y i)) ≤ H)
    (hscale : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 → ∀ p ∈ I,
      2 * V n * H ≤ V (n + 1) * (p * ∏ i, value (u i)))
    (hlarge : ∀ (q : Pg) (y : MovingRegularSlot n r m → σ),
      (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
    (hvg : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
        Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖ := by
  intro ρ greg
  have he := movingAmplitudeOffDiagonal_eq_next_on_coefficients value hvalue outside μ childBound pivotBound V
    hV F hF φ G n r m Pg hPg ρ ν hvg I hI hφsupport hchild hgap
    (fun XR right hr => hlarge XR right hr) hcomp greg ggiant favorable
  rw [← he]
  exact movingTemplatePrimeAmplitude_transfer_on_live value hvalue outside μ childBound pivotBound V F
    φ G n r m Pg I hPg hPI hI hφ hpos hμ hμmass ν sets hsets hcard ggiant favorable
    hgiant H hH hscale hlarge

theorem movingTemplatePrimeAmplitude_step_of_live_coefficients {σ J : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμlower : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n r m : ℕ)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : Pg ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : Pg, ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hcap : ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)⌉₊ ≤ H)
    (hIlower : ∀ p ∈ I, Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (hscale : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 → ∀ p ∈ I,
      2 * V n * H ≤ V (n + 1) * (p * ∏ i, value (u i)))
    (hlarge : ∀ (q : Pg) (y : MovingRegularSlot n r m → σ),
      (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
    (hvg : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G (n + 1) r m
        Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖ := by
  let F₀ := movingOriginalLeaf value q F g Dq S ψ X lo hi
  have hzero : ∀ x, F₀ x 0 = 0 :=
    movingOriginalLeaf_zero value q F hF g Dq S ψ X lo hi
  have hH (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
      (p : ℕ) (hp : p ∈ I) (q' : Pg) (y : MovingRegularSlot n r m → σ)
      (s : transferFrequencyRange (V n))
      (hc : movingTemplateCoefficient value outside μ childBound pivotBound V F₀ φ G
        n (4 + r) m s.val (movingRestoreSample n r m u y) p q' ≠ 0) :
      (q' : ℕ) * (∏ i, value (y i)) ≤ H :=
    (movingTemplateCoefficient_recursive_cell_cap value outside μ childBound pivotBound V
      q F g Dq S ψ X lo hi W hX hwindow φ G c hout hμlower n r m u hu
      s.val y p q' (hIlower p hp) hc).trans hcap
  exact movingTemplatePrimeAmplitude_step_on_coefficients value hvalue outside μ childBound pivotBound V
    hV F₀ hzero φ G n r m Pg I hPg hPI hI hφ hpos hμ hμmass ν sets hsets hcard
    ggiant favorable hgiant H hH hscale hlarge hvg hφsupport hchild hgap hcomp

theorem movingTemplatePrimeAmplitude_step_constructed_coefficients {σ J : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμlower : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n r m : ℕ) (Y reserveMass : ℝ) (hm : 64 ≤ reserveMass) (hY : Y ≤ W)
    (hVeq : V = movingProductNaturalCutoff (movingCellPivotExponent G c) W Y reserveMass)
    (hbudget : ∀ j, 2 * movingCellPivotExponent G c j ≤
      movingProductExponent (movingCellPivotExponent G c) W j)
    (hpositive : 0 ≤ movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : Pg ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : Pg, ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hHeq : H = ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)⌉₊)
    (hIlower : ∀ p ∈ I, Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (hlarge : ∀ (q : Pg) (y : MovingRegularSlot n r m → σ),
      (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
    (hvg : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G (n + 1) r m
        Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖ := by
  have hV : Monotone V := by
    rw [hVeq]
    exact movingProductNaturalCutoff_monotone (movingCellPivotExponent G c) W Y reserveMass hbudget
  have hcap : ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)⌉₊ ≤ H := by rw [hHeq]
  have hscale (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
      (p : ℕ) (hp : p ∈ I) : 2 * V n * H ≤ V (n + 1) * (p * ∏ i, value (u i)) := by
    rw [hVeq, hHeq]
    exact movingProductNaturalCutoff_compensation_scale value μ G c hμlower W Y reserveMass
      hm hY hbudget n hpositive u hu p (hIlower p hp)
  exact movingTemplatePrimeAmplitude_step_of_live_coefficients value hvalue outside μ childBound pivotBound V hV
    q F hF g Dq S ψ X lo hi W hX hwindow φ G c hout hμlower n r m Pg I hPg hPI hI hφ
    hpos hμ hμmass ν sets hsets hcard ggiant favorable hgiant H hcap hIlower hscale
    hlarge hvg hφsupport hchild hgap hcomp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantLiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing zero-weight giant labels preserves the full original law -/
namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantMass_live (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) :
    smoothGiantMass (smoothGiantLivePrimes P φ G) φ G = smoothGiantMass P φ G := by
  unfold smoothGiantMass smoothGiantLivePrimes
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : φ (Real.log p - G) = 0 <;> simp only [h, ne_eq, not_true_eq_false,
    ite_false, if_false, zero_div, not_false_eq_true, ite_true, if_true]

theorem smoothGiantPrior_sum_live (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ) (f : ℕ → ℂ) :
    (∑ p : P, (smoothGiantPrior P φ G p : ℂ) * f p) =
      ∑ p : smoothGiantLivePrimes P φ G,
        (smoothGiantPrior (smoothGiantLivePrimes P φ G) φ G p : ℂ) * f p := by
  have hh (Q : Finset ℕ) :
      (∑ p : Q, (smoothGiantPrior Q φ G p : ℂ) * f p) =
        ∑ p ∈ Q, ((Real.exp (smoothGiantLogNormalizer Q φ G) * φ (Real.log p - G) /
          (p : ℝ) : ℝ) : ℂ) * f p := by
    exact Finset.sum_coe_sort Q (fun p : ℕ =>
      ((Real.exp (smoothGiantLogNormalizer Q φ G) * φ (Real.log p - G) /
        (p : ℝ) : ℝ) : ℂ) * f p)
  rw [hh P, hh (smoothGiantLivePrimes P φ G)]
  simp only [smoothGiantLogNormalizer, smoothGiantMass_live]
  symm
  unfold smoothGiantLivePrimes
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : φ (Real.log p - G) = 0 <;> simp [h]

theorem smoothGiantPrior_double_sum_live (P : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (f : ℕ → ℕ → ℂ) :
    (∑ x : P, (smoothGiantPrior P φ G x : ℂ) *
      ∑ y : P, (smoothGiantPrior P φ G y : ℂ) * f x y) =
    ∑ x : smoothGiantLivePrimes P φ G,
      (smoothGiantPrior (smoothGiantLivePrimes P φ G) φ G x : ℂ) *
      ∑ y : smoothGiantLivePrimes P φ G,
        (smoothGiantPrior (smoothGiantLivePrimes P φ G) φ G y : ℂ) * f x y := by
  rw [smoothGiantPrior_sum_live P φ G
    (fun x => ∑ y : P, (smoothGiantPrior P φ G y : ℂ) * f x y)]
  apply Finset.sum_congr rfl
  intro x _
  rw [smoothGiantPrior_sum_live P φ G (f x)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeLiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact full giant amplitude on its nonzero finite support -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplatePrimeAmplitude_live {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (P : Finset ℕ) (H : ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      P (smoothGiantPrior P φ H) ν greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      (smoothGiantLivePrimes P φ H) (smoothGiantPrior (smoothGiantLivePrimes P φ H) φ H)
      ν greg ggiant favorable := by
  unfold movingTemplatePrimeAmplitude
  exact smoothGiantPrior_double_sum_live P φ H (fun XL XR =>
    ∑ s : transferFrequencyRange (V n),
      ∑ y : MovingRegularSlot n r m → σ, ((∏ i, ν i (y i) : ℝ) : ℂ) *
        (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m
          s.val y XL XR *
          movingTaggedTransform
            (Sum.elim (fun b : Bool => if b then XL else XR) (value ∘ y))
            (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedAlphabetSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact alphabet restriction for the original independent priors -/
namespace Ostmann
open scoped Classical BigOperators

theorem finite_sum_embedding_support {A B M : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid M] (e : B ↪ A) (f : A → M)
    (hf : ∀ a, a ∉ Set.range e → f a = 0) :
    (∑ a, f a) = ∑ b, f (e b) := by
  rw [← Finset.sum_image e.injective.injOn]
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hf a
  simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using ha

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingDiagonalLiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal diagonal is unchanged on removing zero-weight giant labels -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem pivotDiagonal_embedding_support {A B : Type*} [Fintype A] [Fintype B]
    (e : B ↪ A) (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hc : ∀ a, a ∉ Set.range e → c a = 0) :
    pivotDiagonal L v c = pivotDiagonal (L ∘ e) (v ∘ e) (c ∘ e) := by
  unfold pivotDiagonal
  rw [finite_sum_embedding_support e _ (fun a ha => by simp only [hc a ha, zero_mul, ite_self, Finset.sum_const_zero])]
  apply Finset.sum_congr rfl
  intro a _
  exact finite_sum_embedding_support e _ (fun b hb => by simp only [hc b hb, map_zero, mul_zero, ite_self])

theorem smoothGiantPrior_live_embed (P : Finset ℕ) (φ : ℝ → ℝ) (H : ℝ)
    (p : smoothGiantLivePrimes P φ H) :
    smoothGiantPrior (smoothGiantLivePrimes P φ H) φ H p =
      smoothGiantPrior P φ H ⟨p, smoothGiantLivePrimes_subset P φ H p.property⟩ := by
  simp only [smoothGiantPrior, smoothGiantLogNormalizer, smoothGiantMass_live]

theorem movingAmplitudeDiagonal_live {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (P I : Finset ℕ) (H : ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m P I
      (smoothGiantPrior P φ H) ν greg ggiant favorable =
    movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m
      (smoothGiantLivePrimes P φ H) I (smoothGiantPrior (smoothGiantLivePrimes P φ H) φ H)
      ν greg ggiant favorable := by
  let e : MovingAmplitudeIndex σ (smoothGiantLivePrimes P φ H) n r m V ↪
      MovingAmplitudeIndex σ P n r m V :=
    ⟨fun a => (⟨a.1, smoothGiantLivePrimes_subset P φ H a.1.property⟩, a.2), by
      intro a b hab
      rcases a with ⟨a, a'⟩
      rcases b with ⟨b, b'⟩
      have hfirst : a = b := Subtype.ext (congrArg (fun z => (z.1 : ℕ)) hab)
      have hsecond : a' = b' := congrArg Prod.snd hab
      cases hfirst
      cases hsecond
      rfl⟩
  unfold movingAmplitudeDiagonal
  dsimp only
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 2
  have hsupport (a : MovingAmplitudeIndex σ P n r m V) (ha : a ∉ Set.range e) :
      smoothGiantPrior P φ H a.1 = 0 := by
    have hp : (a.1 : ℕ) ∉ smoothGiantLivePrimes P φ H := by
      intro hp
      apply ha
      refine ⟨(⟨a.1, hp⟩, a.2), ?_⟩
      rfl
    have hz : φ (Real.log (a.1 : ℕ) - H) = 0 := by
      by_contra hn
      exact hp (Finset.mem_filter.mpr ⟨a.1.property, hn⟩)
    simp only [smoothGiantPrior, hz, mul_zero, zero_div]
  rw [pivotDiagonal_embedding_support e _ _ _ (fun a ha => by
    simp only [movingTemplateTransferWeight, movingAmplitudePrior, hsupport a ha,
      zero_mul, Complex.ofReal_zero])]
  apply congrArg (pivotDiagonal _ _)
  funext a
  have heval (b : MovingAmplitudeIndex σ (smoothGiantLivePrimes P φ H) n r m V) :
      e b = (⟨b.1, smoothGiantLivePrimes_subset P φ H b.1.property⟩, b.2) := rfl
  simp only [Function.comp_apply, heval, movingTemplateTransferWeight,
    movingAmplitudePrior, smoothGiantPrior_live_embed]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullCoefficientTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient-supported transfer with the full original giant prior -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingTemplatePrimeAmplitude_step_full_coefficients_oai {σ J : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμlower : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n r m : ℕ) (Y reserveMass : ℝ) (hm : 64 ≤ reserveMass) (hY : Y ≤ W)
    (hVeq : V = movingProductNaturalCutoff (movingCellPivotExponent G c) W Y reserveMass)
    (hbudget : ∀ j, 2 * movingCellPivotExponent G c j ≤
      movingProductExponent (movingCellPivotExponent G c) W j)
    (hpositive : 0 ≤ movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : smoothGiantLivePrimes Pg φ (G (n + 1)) ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : smoothGiantLivePrimes Pg φ (G (n + 1)), ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hHeq : H = ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)⌉₊)
    (hIlower : ∀ p ∈ I, Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (hlarge : ∀ (q : smoothGiantLivePrimes Pg φ (G (n + 1))) (y : MovingRegularSlot n r m → σ),
      (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
    (hvg : ∀ q : smoothGiantLivePrimes Pg φ (G (n + 1)), V (n + 1) < (q : ℕ))
    (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : smoothGiantLivePrimes Pg φ (G (n + 1)), ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G (n + 1) r m
        Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖ := by
  dsimp only
  rw [movingTemplatePrimeAmplitude_live (P := Pg),
    movingAmplitudeDiagonal_live (P := Pg),
    movingTemplatePrimeAmplitude_live (P := Pg)]
  have hnorm : smoothGiantLogNormalizer Pg φ (G (n + 1)) =
      smoothGiantLogNormalizer (smoothGiantLivePrimes Pg φ (G (n + 1))) φ (G (n + 1)) := by
    simp only [smoothGiantLogNormalizer, smoothGiantMass_live]
  rw [hnorm]
  exact movingTemplatePrimeAmplitude_step_constructed_coefficients value hvalue outside μ
    childBound pivotBound V q F hF g Dq S ψ X lo hi W hX hwindow φ G c hout hμlower
    n r m Y reserveMass hm hY hVeq hbudget hpositive
    (smoothGiantLivePrimes Pg φ (G (n + 1))) I
    (fun p hp => hPg p (smoothGiantLivePrimes_subset Pg φ (G (n + 1)) hp)) hPI hI hφ
    (by simpa only [smoothGiantMass_live] using hpos) hμ hμmass ν sets hsets hcard
    ggiant favorable hgiant H hHeq hIlower hlarge hvg hφsupport hchild hgap hcomp

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.movingTemplatePrimeAmplitude_step_full_coefficients_oai := @OAI.Ostmann.movingTemplatePrimeAmplitude_step_full_coefficients_oai
