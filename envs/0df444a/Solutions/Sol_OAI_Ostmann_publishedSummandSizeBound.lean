-- Prove2me | solution 1 for OAI.Ostmann.publishedSummandSizeBound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:46:20.03906+00:00
-- url     : https://prove2.me/submissions/01552e18-97a9-4509-8f50-a1ac47cdcf9d

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D006

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Collision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Elementary collision estimates

These are the finite probability and support-size inequalities used in §2
and in the final collision argument of §3. No analytic estimate is assumed.
-/

namespace Ostmann

open scoped BigOperators

/-- Cauchy--Schwarz bounds the collision probability of a unit mass on a
finite nonempty support by the reciprocal of the support's size. -/
theorem inverse_card_le_collision {α : Type*} (s : Finset α) (μ : α → ℝ)
    (hs : s.Nonempty) (hmass : ∑ x ∈ s, μ x = 1) :
    1 / (s.card : ℝ) ≤ ∑ x ∈ s, μ x ^ 2 := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  apply (div_le_iff₀ hc).mpr
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := μ)
  rw [hmass, one_pow] at h
  simpa only [mul_comm] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredSupportProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The centered support projections in the contracting local kernel -/

namespace Ostmann
open scoped Classical BigOperators

theorem finiteSupportMean_spec {α : Type*} (S : Finset α) (f : α → ℂ) :
    (S.card : ℂ) * finiteSupportMean S f = ∑ x ∈ S, f x := by
  by_cases hs : S.card = 0
  · have he : S = ∅ := Finset.card_eq_zero.mp hs
    simp [he, finiteSupportMean]
  · unfold finiteSupportMean
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredProjectionPairing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Self-adjointness of the finite centered and kernel blocks -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem centeredSupportProjection_pairing {α : Type*} [Fintype α]
    (S : Finset α) (f g : α → ℂ) :
    (∑ x, conj (f x) * centeredSupportProjection S g x) =
      ∑ x, conj (centeredSupportProjection S f x) * g x := by
  have hm : (∑ x ∈ S, conj (f x)) * finiteSupportMean S g =
      conj (finiteSupportMean S f) * ∑ x ∈ S, g x := by
    simp only [finiteSupportMean, map_mul, map_inv₀, map_natCast, map_sum]
    ring
  simp only [centeredSupportProjection, mul_zero, apply_ite, map_zero,
    ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [mul_sub, map_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum]
  rw [hm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FiniteKernelCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal residue-point coordinates of the local kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem centeredSupportProjection_sum {α : Type*}
    (S : Finset α) (f : α → ℂ) :
    (∑ x ∈ S, centeredSupportProjection S f x) = 0 := by
  have he : (∑ x ∈ S, centeredSupportProjection S f x) =
      (∑ x ∈ S, f x) - (S.card : ℂ) * finiteSupportMean S f := by
    simp only [centeredSupportProjection]
    rw [Finset.sum_congr rfl (fun x hx => ite_eq_left hx), Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [he, finiteSupportMean_spec, sub_self]

theorem centeredSupportProjection_idempotent {α : Type*}
    (S : Finset α) (f : α → ℂ) :
    centeredSupportProjection S (centeredSupportProjection S f) = centeredSupportProjection S f := by
  have hm : finiteSupportMean S (centeredSupportProjection S f) = 0 := by
    rw [finiteSupportMean, centeredSupportProjection_sum, mul_zero]
  funext x
  by_cases hx : x ∈ S
  · simp only [centeredSupportProjection, ite_eq_left hx, hm, sub_zero]
  · simp only [centeredSupportProjection, ite_eq_right hx]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelCoordinateIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact identification of the centered-coordinate kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem centeredSupportProjection_pairing_range {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (f g : ZMod p → ℂ) :
    (∑ x, conj (centeredSupportProjection S f x) * centeredSupportProjection S g x) =
      ∑ x, conj (centeredSupportProjection S f x) * g x := by
  rw [centeredSupportProjection_pairing, centeredSupportProjection_idempotent]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_TruncatedModePairing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pairing the truncated kernel against only its active centered modes -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators ComplexConjugate

theorem countingVectorNorm_sq {α : Type*} [Fintype α] (f : α → ℂ) :
    countingVectorNorm f ^ 2 = ∑ x, ‖f x‖ ^ 2 := EuclideanSpace.norm_sq_eq _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_AveragedKernelPairing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the actual tensor coordinates over summand elements -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem kernelPairing_sum_left {ι α β : Type*} [Fintype α] [Fintype β]
    (A : Finset ι) (V : ι → α → ℂ) (g : β → ℂ) (M : α → β → ℂ) :
    kernelPairingLinearMap (fun x => ∑ a ∈ A, V a x) g M =
      ∑ a ∈ A, kernelPairingLinearMap (V a) g M := by
  change (∑ x, conj (∑ a ∈ A, V a x) * ∑ y, M x y * g y) = _
  simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem kernelPairing_sum_right {ι α β : Type*} [Fintype α] [Fintype β]
    (A : Finset ι) (f : α → ℂ) (V : ι → β → ℂ) (M : α → β → ℂ) :
    kernelPairingLinearMap f (fun y => ∑ a ∈ A, V a y) M =
      ∑ a ∈ A, kernelPairingLinearMap f (V a) M := by
  change (∑ x, conj (f x) * ∑ y, M x y * ∑ a ∈ A, V a y) = _
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := A)]
  change _ = ∑ a ∈ A, ∑ x, conj (f x) * ∑ y, M x y * V a y
  simp only [Finset.mul_sum]

theorem kernelPairing_const_mul {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) (M : α → β → ℂ) (c d : ℂ) :
    kernelPairingLinearMap (fun x => c * f x) (fun y => d * g y) M =
      conj c * d * kernelPairingLinearMap f g M := by
  change (∑ x, conj (c * f x) * ∑ y, M x y * (d * g y)) =
    conj c * d * ∑ x, conj (f x) * ∑ y, M x y * g y
  simp only [map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem kernelPairing_averages {ι κ α β : Type*} [Fintype α] [Fintype β]
    (A : Finset ι) (B : Finset κ) (V : ι → α → ℂ) (W : κ → β → ℂ)
    (M : α → β → ℂ) :
    kernelPairingLinearMap (averagedCoordinates A V) (averagedCoordinates B W) M =
      (A.card : ℂ)⁻¹ * (B.card : ℂ)⁻¹ *
        ∑ a ∈ A, ∑ b ∈ B, kernelPairingLinearMap (V a) (W b) M := by
  change kernelPairingLinearMap (fun x => (A.card : ℂ)⁻¹ * ∑ a ∈ A, V a x)
    (fun y => (B.card : ℂ)⁻¹ * ∑ b ∈ B, W b y) M = _
  rw [kernelPairing_const_mul]
  simp only [map_inv₀, map_natCast, kernelPairing_sum_left, kernelPairing_sum_right]
  rw [Finset.sum_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CenteredRamanujanKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local Ramanujan identity for the centered-coordinate budget -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem centeredPoint_pairing {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ S) :
    (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
      centeredSupportProjection S (residuePointVector b) x) =
        (if a = b then 1 else 0) - (S.card : ℂ)⁻¹ := by
  rw [centeredSupportProjection_pairing_range]
  simp [centeredSupportProjection, residuePointVector, finiteSupportMean, ha, hb, eq_comm]

theorem nonzero_character_difference_sum {p : ℕ} [NeZero p] (a b : ZMod p) :
    (∑ h ∈ Finset.univ.erase 0, ZMod.stdAddChar (h * (a - b))) =
      (if a = b then (p : ℂ) else 0) - 1 := by
  have he := Finset.sum_erase_add Finset.univ (fun h => ZMod.stdAddChar (h * (a - b)))
    (Finset.mem_univ (0 : ZMod p))
  rw [AddChar.sum_mulShift (a - b) (ZMod.isPrimitive_stdAddChar p)] at he
  simp only [zero_mul, AddChar.map_zero_eq_one, ZMod.card, sub_eq_zero] at he
  by_cases hab : a = b <;> simpa only [hab, ite_true, if_true, ite_false, if_false, Nat.cast_zero] using
    eq_sub_of_add_eq he

theorem centeredRamanujanKernel {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ S) :
    (∑ h ∈ Finset.univ.erase 0, ZMod.stdAddChar (h * (a - b))) =
      ((p : ℂ) / S.card - 1) + p *
        ∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
          centeredSupportProjection S (residuePointVector b) x := by
  rw [nonzero_character_difference_sum, centeredPoint_pairing S a b ha hb]
  split_ifs <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_FiniteCoordinateEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The energy of averaged finite tensor coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem kernelPairing_identity {α : Type*} [Fintype α] (f g : α → ℂ) :
    kernelPairingLinearMap f g (fun x y => if y = x then 1 else 0) =
      ∑ x, conj (f x) * g x := by
  change (∑ x, conj (f x) * ∑ y, (if y = x then 1 else 0) * g y) = _
  simp

theorem averagedCoordinates_inner {ι κ α : Type*} [Fintype α]
    (A : Finset ι) (B : Finset κ) (V : ι → α → ℂ) (W : κ → α → ℂ) :
    (∑ x, conj (averagedCoordinates A V x) * averagedCoordinates B W x) =
      (A.card : ℂ)⁻¹ * (B.card : ℂ)⁻¹ *
        ∑ a ∈ A, ∑ b ∈ B, ∑ x, conj (V a x) * W b x := by
  have hh := kernelPairing_averages A B V W (fun x y => if y = x then 1 else 0)
  simpa only [kernelPairing_identity] using hh

theorem countingVectorNorm_sq_complex {α : Type*} [Fintype α] (f : α → ℂ) :
    ((countingVectorNorm f ^ 2 : ℝ) : ℂ) = ∑ x, conj (f x) * f x := by
  rw [countingVectorNorm_sq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [Complex.ofReal_pow, mul_comm] using (Complex.mul_conj' (f x)).symm

theorem productVector_inner {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f g : ∀ i, α i → ℂ) :
    (∑ x : (∀ i, α i), conj (∏ i, f i (x i)) * ∏ i, g i (x i)) =
      ∏ i, ∑ x, conj (f i x) * g i x := by
  simp only [map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => conj (f i x) * g i x)).symm

theorem centeredSubsetEnergy_formula {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (T : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) :
    (centeredSubsetEnergy p S T A a : ℂ) =
      (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
        ∏ i ∈ T, ∑ z, conj (centeredSupportProjection (S i) (residuePointVector (a x i)) z) *
          centeredSupportProjection (S i) (residuePointVector (a y i)) z := by
  rw [centeredSubsetEnergy, countingVectorNorm_sq_complex, averagedCoordinates_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hh := productVector_inner (ι := T) (α := fun i : T => ZMod (p i))
    (fun i z => centeredSupportProjection (S i) (residuePointVector (a x i)) z)
    (fun i z => centeredSupportProjection (S i) (residuePointVector (a y i)) z)
  unfold centeredSubsetVector
  have hp := Finset.prod_coe_sort T (fun i : Fin n => ∑ z : ZMod (p i),
    conj (centeredSupportProjection (S i) (residuePointVector (a x i)) z) *
      centeredSupportProjection (S i) (residuePointVector (a y i)) z)
  convert hh.trans hp using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr
  · ext z
    simp
  · intro z _
    rfl

theorem centeredSubsetEnergy_nonneg {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (T : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) :
    0 ≤ centeredSubsetEnergy p S T A a := sq_nonneg _

theorem centeredSubsetEnergy_empty {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) {ι : Type*}
    (A : Finset ι) (hA : A.Nonempty) (a : ι → ∀ i, ZMod (p i)) :
    centeredSubsetEnergy p S ∅ A a = 1 := by
  have hAc : (A.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  rw [centeredSubsetEnergy, countingVectorNorm_sq]
  simp [averagedCoordinates, centeredSubsetVector, hAc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorRamanujanExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expansion of the reduced-frequency kernel by centered subset modes -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem tensorRamanujan_expansion {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (R : Finset (Fin n))
    (a b : ∀ i, ZMod (p i)) (ha : ∀ i ∈ R, a i ∈ S i) (hb : ∀ i ∈ R, b i ∈ S i) :
    (∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)), ZMod.stdAddChar (h * (a i - b i))) =
      ∑ T ∈ R.powerset,
        (∏ i ∈ T, (p i : ℂ)) * (∏ i ∈ R \ T, ((p i : ℂ) / (S i).card - 1)) *
          ∏ i ∈ T, centeredResidueGram (S i) (a i) (b i) := by
  calc
    _ = ∏ i ∈ R, ((p i : ℂ) * centeredResidueGram (S i) (a i) (b i) +
        ((p i : ℂ) / (S i).card - 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [centeredRamanujanKernel (S i) (a i) (b i) (ha i hi) (hb i hi)]
      unfold centeredResidueGram
      ring
    _ = _ := by
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.prod_mul_distrib]
      ring

theorem tensorRamanujan_energy_expansion {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (R : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) (ha : ∀ x ∈ A, ∀ i ∈ R, a x i ∈ S i) :
    (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
      (∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)), ZMod.stdAddChar (h * (a x i - a y i))) =
        ∑ T ∈ R.powerset, (∏ i ∈ T, (p i : ℂ)) *
          (∏ i ∈ R \ T, ((p i : ℂ) / (S i).card - 1)) *
            (centeredSubsetEnergy p S T A a : ℂ) := by
  have he (x) (hx : x ∈ A) (y) (hy : y ∈ A) :=
    tensorRamanujan_expansion p S R (a x) (a y) (ha x hx) (ha y hy)
  calc
    _ = (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
        ∑ T ∈ R.powerset, (∏ i ∈ T, (p i : ℂ)) *
          (∏ i ∈ R \ T, ((p i : ℂ) / (S i).card - 1)) *
            ∏ i ∈ T, centeredResidueGram (S i) (a x i) (a y i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_congr rfl (fun y hy => he x hx y hy)
    _ = _ := by
      simp_rw [Finset.sum_comm (s := A) (t := R.powerset)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      rw [centeredSubsetEnergy_formula]
      simp only [centeredResidueGram, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TupleCRTFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cofactor arguments for the Fourier transform of a prime tuple -/

namespace Ostmann

open scoped BigOperators Classical

private theorem stdAddChar_factor {a b M : ℕ} [NeZero a] [NeZero b] [NeZero M]
    (hM : a * b = M) (n : ℕ) :
    ZMod.stdAddChar ((b * n : ℕ) : ZMod M) =
      ZMod.stdAddChar (n : ZMod a) := by
  have hl : ((b * n : ℕ) : ZMod M) = ((b * n : ℕ) : ℤ) := by simp
  have hr : (n : ZMod a) = (n : ℤ) := by simp
  rw [hl, hr, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [← hM, Nat.cast_mul]
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne b
  field_simp

theorem tuple_stdAddChar {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (x : ZMod (∏ i, p i)) :
    ZMod.stdAddChar x = ∏ i, ZMod.stdAddChar
      ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc x i) := by
  let a (i : I) : ZMod (p i) :=
    (tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc x i
  have hx : x = ∑ i, (tupleCofactor p i : ZMod (∏ i, p i)) * (a i).val := by
    apply (ZMod.prodEquivPi p hc).injective
    ext j
    simp only [map_sum, map_mul, map_natCast, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply]
    rw [Finset.sum_eq_single j]
    · have hu := (ZMod.isUnit_iff_coprime (tupleCofactor p j) (p j)).mpr
        (tupleCofactor_coprime p hc j)
      simp only [ZMod.natCast_zmod_val, a]
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul]
    · intro i _ hij
      have hd : p j ∣ tupleCofactor p i :=
        Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
      have hz : (tupleCofactor p i : ZMod (p j)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hd
      simp only [hz, zero_mul]
    · simp
  have hsum (s : Finset I) :
      ZMod.stdAddChar (∑ i ∈ s, (tupleCofactor p i : ZMod (∏ i, p i)) * ((a i).val : ZMod (∏ i, p i))) =
        ∏ i ∈ s, ZMod.stdAddChar ((tupleCofactor p i : ZMod (∏ i, p i)) * ((a i).val : ZMod (∏ i, p i))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]
  conv_lhs => rw [hx, hsum]
  apply Finset.prod_congr rfl
  intro i _
  have hpos : 0 < tupleCofactor p i :=
    Finset.prod_pos (fun j _ => NeZero.pos (p j))
  let : NeZero (tupleCofactor p i) := ⟨hpos.ne'⟩
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using
    (stdAddChar_factor (tupleCofactor_mul p i) (a i).val)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_UnitRamanujanProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reduced-frequency kernel factors over the actual CRT moduli -/

namespace Ostmann
open scoped Classical BigOperators

theorem unitRamanujanKernel_int_congr {q r : ℕ} [NeZero q] [NeZero r]
    (h : q = r) (z : ℤ) :
    unitRamanujanKernel q (z : ZMod q) = unitRamanujanKernel r (z : ZMod r) := by
  subst r
  rfl

theorem unitRamanujanKernel_scale (q : ℕ) [NeZero q] (c : (ZMod q)ˣ) (z : ZMod q) :
    (∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((c : ZMod q) * (u : ZMod q) * z)) =
      unitRamanujanKernel q z := by
  exact (Equiv.mulLeft c).bijective.sum_comp (fun u : (ZMod q)ˣ =>
    ZMod.stdAddChar ((u : ZMod q) * z))

theorem unitRamanujanKernel_prime {p : ℕ} [Fact p.Prime] (z : ZMod p) :
    unitRamanujanKernel p z =
      ∑ h ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (h * z) := by
  apply Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p))
  · intro u _
    exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
  · intro u _ v _ huv
    exact Units.val_injective huv
  · intro x hx
    exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl

theorem unitRamanujanKernel_product {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (n : ℤ) :
    unitRamanujanKernel (∏ i, p i) (n : ZMod (∏ i, p i)) =
      ∏ i, unitRamanujanKernel (p i) (n : ZMod (p i)) := by
  have he (u : (ZMod (∏ i, p i))ˣ) :
      ZMod.stdAddChar ((u : ZMod (∏ i, p i)) * (n : ZMod (∏ i, p i))) =
        ∏ i, ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
          (crtUnitEquiv p hc u i : ZMod (p i)) * (n : ZMod (p i))) := by
    rw [tuple_stdAddChar p hc]
    apply Finset.prod_congr rfl
    intro i _
    simp only [map_mul, map_intCast, Pi.mul_apply, Pi.intCast_apply]
    change ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
      ((crtUnitEquiv p hc u i : ZMod (p i)) * (n : ZMod (p i)))) = _
    congr 1
    ring
  unfold unitRamanujanKernel
  simp_rw [he]
  have hh := (crtUnitEquiv p hc).toEquiv.sum_comp (fun u : ∀ i, (ZMod (p i))ˣ =>
    ∏ i, ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
      (u i : ZMod (p i)) * (n : ZMod (p i))))
  calc
    _ = ∑ u : (∀ i, (ZMod (p i))ˣ), ∏ i,
        ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
          (u i : ZMod (p i)) * (n : ZMod (p i))) := hh
    _ = ∏ i, ∑ u : (ZMod (p i))ˣ,
        ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
          (u : ZMod (p i)) * (n : ZMod (p i))) := (Fintype.prod_sum (fun i (u : (ZMod (p i))ˣ) =>
            ZMod.stdAddChar ((tupleCofactor p i : ZMod (p i))⁻¹ *
              (u : ZMod (p i)) * (n : ZMod (p i))))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      let c := ZMod.unitOfCoprime (tupleCofactor p i) (tupleCofactor_coprime p hc i)
      have hcval : ((c⁻¹ : (ZMod (p i))ˣ) : ZMod (p i)) =
          (tupleCofactor p i : ZMod (p i))⁻¹ := by
        rw [← ZMod.inv_coe_unit]
        simp only [c, ZMod.coe_unitOfCoprime]
      rw [← hcval]
      exact unitRamanujanKernel_scale (p i) c⁻¹ (n : ZMod (p i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-divisor budget in the collision argument

A distinct pair of integers at distance at most `X` contributes at most
`log X` to the sum of `log p` over primes at which it collides. This is the
elementary counting step behind the larger-sieve use in §§2–3.
-/

namespace Ostmann

open scoped BigOperators

/-- The off-diagonal prime-collision budget, in the ordered-pair convention. -/
theorem sum_log_congruent_primes_le_of_sub_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hdiff : y - x ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) := by
  have hpos : 0 < y - x := Nat.sub_pos_of_lt hxy
  have hbudget := sum_log_prime_divisors_le (P.filter (fun p => x ≡ y [MOD p])) hpos
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2.dvd')
  exact hbudget.trans (Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast hdiff))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_OrdinaryPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordinary prime interval and its normalization

The conductor-one character is trivial, so the ordinary prime prior has
no Page correction. Its logarithmic interval mass and inverse bound are
derived from the same published theta input.
-/

namespace Ostmann

open Filter MeasureTheory

theorem PublishedProgressionInput.localZero_one (P : PublishedProgressionInput) :
    P.localZero 1 = none := by
  cases he : P.localZero 1 with
  | none => rfl
  | some e => exact False.elim (e.modulus_ne_one (Nat.dvd_one.mp (P.divides 1 e he)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_AdditiveSieveProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The additive large sieve for a uniform measure on an actual interval subset -/

namespace Ostmann
open scoped Classical BigOperators

theorem intervalSetReducedEnergy_nonneg {M : ℕ} (A : Finset (Fin M))
    (J : ℤ) (q : ℕ) : 0 ≤ intervalSetReducedEnergy A J q := by
  exact Finset.sum_nonneg (fun h _ => sq_nonneg _)

/-- No density or distribution assumption on the interval subset is needed. -/
theorem additiveSieve_probability_bound (ls : PublishedAdditiveLargeSieve)
    {M Q : ℕ} (hM : 1 ≤ M) (hQ : 1 ≤ Q) (A : Finset (Fin M))
    (hA : A.Nonempty) (J : ℤ) :
    (∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  let c : Fin M → ℂ := fun n => if n ∈ A then 1 else 0
  have hc (q h : ℕ) : additiveSieveSum c J q h = intervalSetExponentialSum A J q h := by
    simp [additiveSieveSum, intervalSetExponentialSum, c]
  have hn : (∑ n, ‖c n‖ ^ 2) = (A.card : ℝ) := by
    have he (n : Fin M) : ‖c n‖ ^ 2 = if n ∈ A then (1 : ℝ) else 0 := by
      by_cases h : n ∈ A <;> simp [c, h]
    simp [he]
  have hh := ls M Q hM hQ J c
  simp only [hc, hn] at hh
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
  calc
    _ = ((A.card : ℝ)⁻¹) ^ 2 *
        ∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q,
          ‖intervalSetExponentialSum A J q h‖ ^ 2 := by
      simp only [intervalSetReducedEnergy, norm_mul, norm_inv, Complex.norm_natCast,
        mul_pow, Finset.mul_sum]
    _ ≤ ((A.card : ℝ)⁻¹) ^ 2 * (((M : ℝ) + (Q : ℝ) ^ 2) * A.card) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by field_simp

theorem sieveAdditivePhase_eq_stdAddChar (q : ℕ) [NeZero q] (h : ℕ) (n : ℤ) :
    sieveAdditivePhase q h n = ZMod.stdAddChar ((h : ZMod q) * (n : ZMod q)) := by
  have hh : (h : ZMod q) * (n : ZMod q) = (((h : ℤ) * n : ℤ) : ZMod q) := by
    push_cast
    rfl
  rw [hh, ZMod.stdAddChar_coe]
  unfold sieveAdditivePhase
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReducedFrequencyEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduced-frequency energy of a uniform set and its Ramanujan kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem unitFrequencyEnergy_kernel {q : ℕ} [NeZero q] {ι : Type*}
    (A : Finset ι) (a : ι → ZMod q) :
    (unitFrequencyEnergy A a : ℂ) =
      (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ *
        ∑ x ∈ A, ∑ y ∈ A, unitRamanujanKernel q (a x - a y) := by
  have hp (u : (ZMod q)ˣ) :
      ((‖(A.card : ℂ)⁻¹ * ∑ x ∈ A, ZMod.stdAddChar ((u : ZMod q) * a x)‖ ^ 2 : ℝ) : ℂ) =
        (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
          ZMod.stdAddChar ((u : ZMod q) * (a x - a y)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj]
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [show (u : ZMod q) * (a x - a y) =
      (u : ZMod q) * a x + -((u : ZMod q) * a y) by ring,
      AddChar.map_add_eq_mul]
    ring
  rw [unitFrequencyEnergy, Complex.ofReal_sum]
  simp_rw [hp]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := A)]
  rfl

theorem sum_reducedNumerators_eq_units {q : ℕ} [NeZero q]
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ h ∈ reducedNumerators q, f h) = ∑ u : (ZMod q)ˣ, f (u : ZMod q).val := by
  change (∑ h ∈ reducedResidues q, f h) = _
  rw [← Finset.sum_coe_sort]
  exact ((unitReducedResidueEquiv q).sum_comp (fun a => f a.val)).symm

theorem intervalSetReducedEnergy_eq_unitFrequencyEnergy {M q : ℕ} [NeZero q]
    (A : Finset (Fin M)) (J : ℤ) :
    intervalSetReducedEnergy A J q =
      unitFrequencyEnergy A (fun n => ((J + (n.val : ℤ) : ℤ) : ZMod q)) := by
  unfold intervalSetReducedEnergy unitFrequencyEnergy
  rw [sum_reducedNumerators_eq_units]
  apply Finset.sum_congr rfl
  intro u _
  simp only [intervalSetExponentialSum, sieveAdditivePhase_eq_stdAddChar,
    ZMod.natCast_zmod_val]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Basic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sets in Ostmann's inverse Goldbach problem

We use `ℕ` for the manuscript's nonnegative integers. The threshold convention
uses `N ≤ n`; changing finitely many initial values does not affect it.
-/

namespace Ostmann

theorem sumset_comm (A B : Set ℕ) : sumset A B = sumset B A := by
  ext n
  simp only [mem_sumset]
  constructor <;> rintro ⟨a, ha, b, hb, hab⟩
  · exact ⟨b, hb, a, ha, (Nat.add_comm b a).trans hab⟩
  · exact ⟨b, hb, a, ha, (Nat.add_comm b a).trans hab⟩

theorem EventuallyPrimeSumset.symm {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) : EventuallyPrimeSumset B A := by
  simpa only [EventuallyPrimeSumset, sumset_comm B A] using h

open scoped symmDiff

/-- Each sufficiently large sum of elements of the summands is prime. -/
theorem EventuallyPrimeSumset.prime_add {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ a ∈ A, ∀ b ∈ B, N ≤ a + b → (a + b).Prime := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun a ha b hb hab => (hN (a + b) hab).mp ⟨a, ha, b, hb, rfl⟩⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SkewKernelSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite algebraic identity for the large-sieve kernel

This is the cancellation underlying Montgomery--Vaughan's equation (3.6).
The diagonal correction is retained explicitly before any norm estimate.
-/

namespace Ostmann

open scoped BigOperators

section
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

 theorem skew_kernel_square_entry (h k : ι → ι → K)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (∑ r, h r s * h r t) =
      (if s = t then ∑ r, h r s ^ 2 else 0) +
        h s t * ((∑ r, k r s) - ∑ r, k r t) + 2 * h s t * k s t := by
  by_cases hst : s = t
  · subst t
    simp [hdiag, sq]
  · have he (r : ι) : h r s * h r t = h s t * (k r s - k r t) +
        (if r = s then h s t * k s t else 0) +
        (if r = t then h s t * k s t else 0) := by
      by_cases hrs : r = s
      · subst r
        simp [hdiag, kdiag, hst]
      · by_cases hrt : r = t
        · subst r
          rw [hdiag, kdiag, kskew t s]
          simp only [hrs, ↓reduceIte]
          ring
        · simp only [hrs, hrt, ↓reduceIte, add_zero]
          exact htriple r s t hrs hrt hst
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [hst, ↓reduceIte, zero_add, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted prime collisions

The elementary weighted pair count used in Lemma 2.5 (collision stability).
The diagonal is paid for by the largest atom; unequal pairs are paid for by
one logarithm of the interval length.
-/

namespace Ostmann

open scoped BigOperators

theorem primeCollisionWeight_self (P : Finset ℕ) (a : ℕ) :
    primeCollisionWeight P a a = ∑ p ∈ P, Real.log (p : ℝ) := by
  simp [primeCollisionWeight, Nat.ModEq.refl]

theorem primeCollisionWeight_symm (P : Finset ℕ) (a b : ℕ) :
    primeCollisionWeight P a b = primeCollisionWeight P b a := by
  unfold primeCollisionWeight
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ => ⟨fun h => h.symm, fun h => h.symm⟩)

/-- The weighted pair count from an off-diagonal logarithmic budget. -/
theorem weighted_prime_collision_bound_of_budget (P S : Finset ℕ) (μ : ℕ → ℝ) (L m : ℝ)
    (hL : 0 ≤ L) (hP : ∀ p ∈ P, p.Prime) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m)
    (hbudget : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → primeCollisionWeight P a b ≤ L) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      L + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  classical
  let W : ℝ := ∑ p ∈ P, Real.log (p : ℝ)
  have hW : 0 ≤ W := Finset.sum_nonneg (fun p hp => Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))
  have hpair : ∀ a ∈ S, ∀ b ∈ S,
      primeCollisionWeight P a b ≤ L + if a = b then W else 0 := by
    intro a ha b hb
    by_cases hab : a = b
    · subst b
      simp only [primeCollisionWeight_self, ite_true, if_true]
      dsimp [W] at *
      linarith
    · simpa [hab] using hbudget a ha b hb hab
  have hsquares : (∑ a ∈ S, μ a ^ 2) ≤ m := by
    calc
      (∑ a ∈ S, μ a ^ 2) ≤ ∑ a ∈ S, m * μ a := by
        apply Finset.sum_le_sum
        intro a ha
        nlinarith [hμ a ha, hatom a ha]
      _ = m := by rw [← Finset.mul_sum, hmass, mul_one]
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, μ a * μ b * (L + if a = b then W else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hpair a ha b hb) (mul_nonneg (hμ a ha) (hμ b hb))
    _ = L + W * ∑ a ∈ S, μ a ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hconstant : (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * L) = L := by
        calc
          _ = ∑ a ∈ S, μ a * (∑ b ∈ S, μ b) * L := by
            apply Finset.sum_congr rfl
            intro a _
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ = L := by
            rw [hmass]
            simp only [mul_one]
            rw [← Finset.sum_mul, hmass, one_mul]
      rw [hconstant]
      congr 1
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq]
      calc
        (∑ a ∈ S, if a ∈ S then μ a * μ a * W else 0) =
            ∑ a ∈ S, W * μ a ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [ha, ite_true, if_true]
          ring
        _ = W * ∑ a ∈ S, μ a ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ L + W * m := add_le_add_right (mul_le_mul_of_nonneg_left hsquares hW) L
    _ = _ := by dsimp [W]; ring

/-- The collision budget depends on the diameter, not the position of the
interval. This is needed for the translated square-root populations in §3. -/
theorem primeCollisionWeight_le_log_of_dist {P : Finset ℕ} {a b X : ℕ}
    (hab : a ≠ b) (hD : Nat.dist a b ≤ X) (hP : ∀ p ∈ P, p.Prime) :
    primeCollisionWeight P a b ≤ Real.log (X : ℝ) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · apply sum_log_congruent_primes_le_of_sub_le P hab _ hP
    rwa [Nat.dist_eq_sub_of_le hab.le] at hD
  · rw [primeCollisionWeight_symm]
    apply sum_log_congruent_primes_le_of_sub_le P hba _ hP
    rwa [Nat.dist_eq_sub_of_le_right hba.le] at hD

/-- Weighted larger-sieve pair bound for an arbitrary interval of diameter `X`. -/
theorem weighted_prime_collision_bound_of_diameter (P S : Finset ℕ) (μ : ℕ → ℝ)
    (X : ℕ) (m : ℝ) (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hD : ∀ a ∈ S, ∀ b ∈ S, Nat.dist a b ≤ X) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) :=
  weighted_prime_collision_bound_of_budget P S μ (Real.log X) m
    (Real.log_nonneg (by exact_mod_cast hX)) hP hμ hmass hatom
    (fun a ha b hb hab => primeCollisionWeight_le_log_of_dist hab (hD a ha b hb) hP)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Projection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residue projection of finite probability measures

These identities connect the pair count in `WeightedCollision` with the
collision norm of a projected measure, as used in Lemma 2.5 of the paper.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_fiberMass_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β) (F : β → ℝ)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y * F y = ∑ a ∈ s, μ a * F (f a) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hf (fun a => μ a * F (f a))]
  apply Finset.sum_congr rfl
  intro y _
  unfold fiberMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

theorem sum_fiberMass {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y = ∑ a ∈ s, μ a := by
  simpa only [mul_one] using sum_fiberMass_mul s t μ f (fun _ => 1) hf

theorem sum_fiberMass_sq {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, (fiberMass s μ f y) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if f a = f b then μ a * μ b else 0 := by
  classical
  simp only [pow_two]
  rw [sum_fiberMass_mul s t μ f (fiberMass s μ f) hf]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberMass, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro b _
  simp only [eq_comm]

theorem residueMass_sq (s : Finset ℕ) (μ : ℕ → ℝ) {p : ℕ}
    (hp : 0 < p) :
    ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if a ≡ b [MOD p] then μ a * μ b else 0 :=
  sum_fiberMass_sq s (Finset.range p) μ (fun a => a % p)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt a hp))

/-- Reorder the weighted residue collisions as a sum over integer pairs. -/
theorem weighted_residueMass_sq (P s : Finset ℕ) (μ : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) =
    ∑ a ∈ s, ∑ b ∈ s, μ a * μ b * primeCollisionWeight P a b := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ a ∈ s, ∑ b ∈ s,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [residueMass_sq s μ (hP p hp).pos]
      simp only [Finset.mul_sum]
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ p ∈ P,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [primeCollisionWeight, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring

/-- The projected bound for a translated interval uses only its diameter. -/
theorem residue_collision_bound_of_diameter (P s : Finset ℕ) (μ : ℕ → ℝ)
    (X : ℕ) (m : ℝ) (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hD : ∀ a ∈ s, ∀ b ∈ s, Nat.dist a b ≤ X) (hμ : ∀ a ∈ s, 0 ≤ μ a)
    (hmass : ∑ a ∈ s, μ a = 1) (hatom : ∀ a ∈ s, μ a ≤ m) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  rw [weighted_residueMass_sq P s μ hP]
  exact weighted_prime_collision_bound_of_diameter P s μ X m hX hP hD hμ hmass hatom

/-- Residue labels may be changed (in particular, negated) without changing
the collision norm, provided they identify exactly the congruent pairs. -/
theorem fiberMass_sq_eq_residueMass_sq (s t : Finset ℕ) (μ : ℕ → ℝ)
    (f : ℕ → ℕ) {p : ℕ} (hp : 0 < p)
    (hf : ∀ a ∈ s, f a ∈ t)
    (hcongr : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ a ≡ b [MOD p]) :
    (∑ r ∈ t, (fiberMass s μ f r) ^ 2) =
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 := by
  rw [sum_fiberMass_sq s t μ f hf, residueMass_sq s μ hp]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [hcongr a ha b hb]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Residues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complementary residue supports

The elementary reduction in §2 of the manuscript. Only the exclusion of
composite sums is used to separate the tail supports at a prime.
-/

namespace Ostmann

/-- Large sums in an eventual prime decomposition have no smaller prime divisor. -/
theorem EventuallyPrimeSumset.prime_not_dvd_large_sum {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ p, p.Prime → ∀ a ∈ A, ∀ b ∈ B,
      N ≤ a + b → p < a + b → ¬ p ∣ a + b := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro p hp a ha b hb hn hlt hdvd
  have hab : (a + b).Prime := (hN _ hn).mp ⟨a, ha, b, hb, rfl⟩
  have heq : a + b = p := (hab.dvd_iff_eq (ne_of_gt hp.one_lt)).mp hdvd
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootCollisions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collisions of uniform root populations

The root populations at the end of §3 occupy translated intervals. Their
collision upper bound depends on the diameter and their cardinality.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_uniform_mass (s : Finset ℕ) (hs : s.Nonempty) :
    (∑ _a ∈ s, (1 / (s.card : ℝ))) = 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_one_div_cancel hc

theorem uniformResidueCollision_upper (P s : Finset ℕ) (hs : s.Nonempty)
    (D : ℕ) (hD : 1 ≤ D) (hP : ∀ p ∈ P, p.Prime)
    (hdiam : ∀ a ∈ s, ∀ b ∈ s, Nat.dist a b ≤ D) :
    (∑ p ∈ P, Real.log (p : ℝ) * uniformResidueCollision s p) ≤
      Real.log (D : ℝ) + (1 / (s.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) := by
  exact residue_collision_bound_of_diameter P s (fun _ => 1 / (s.card : ℝ)) D
    (1 / (s.card : ℝ)) hD hP hdiam (fun _ _ => by positivity)
    (sum_uniform_mass s hs) (fun _ _ => le_rfl)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SubsetReducedEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact positive subset expansion of the classical reduced energy -/

namespace Ostmann
open scoped Classical BigOperators

theorem unitRamanujanKernel_subset {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (R : Finset (Fin n)) [NeZero (∏ i ∈ R, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (z : ℤ) :
    unitRamanujanKernel (∏ i ∈ R, p i) (z : ZMod (∏ i ∈ R, p i)) =
      ∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)),
        ZMod.stdAddChar (h * (z : ZMod (p i))) := by
  let : NeZero (∏ i : R, p i) := ⟨by
    rw [Finset.prod_coe_sort]
    exact NeZero.ne _⟩
  have hcR : Pairwise (fun i j : R => (p i).Coprime (p j)) := by
    intro i j hij
    exact hc (fun he => hij (Subtype.ext he))
  have hh := unitRamanujanKernel_product (fun i : R => p i) hcR z
  simp_rw [unitRamanujanKernel_prime] at hh
  have hq := Finset.prod_coe_sort R p
  have hr := Finset.prod_coe_sort R (fun i =>
    ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)), ZMod.stdAddChar (h * (z : ZMod (p i))))
  rw [unitRamanujanKernel_int_congr hq z, hr] at hh
  exact hh

theorem subsetSieveCoefficient_nonneg {n : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (R T : Finset (Fin n))
    (hS : ∀ i ∈ R, (S i).Nonempty) :
    0 ≤ subsetSieveCoefficient p S R T := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  · apply Finset.prod_nonneg
    intro i hi
    have hcard : (0 : ℝ) < (S i).card := by
      exact_mod_cast Finset.card_pos.mpr (hS i (Finset.mem_sdiff.mp hi).1)
    have hle : ((S i).card : ℝ) ≤ p i := by
      exact_mod_cast (Finset.card_le_univ (S i)).trans_eq (ZMod.card (p i))
    exact sub_nonneg.mpr ((le_div_iff₀ hcard).mpr (by simpa using hle))

theorem subset_reduced_energy_expansion {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (S : ∀ i, Finset (ZMod (p i)))
    (R : Finset (Fin n)) [NeZero (∏ i ∈ R, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) {ι : Type*}
    (A : Finset ι) (a : ι → ℤ)
    (ha : ∀ x ∈ A, ∀ i ∈ R, (a x : ZMod (p i)) ∈ S i) :
    unitFrequencyEnergy A (fun x => (a x : ZMod (∏ i ∈ R, p i))) =
      ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
        centeredSubsetEnergy p S T A (fun x i => (a x : ZMod (p i))) := by
  apply Complex.ofReal_injective
  rw [unitFrequencyEnergy_kernel]
  have hk (x y : ι) :
      unitRamanujanKernel (∏ i ∈ R, p i)
          ((a x : ZMod (∏ i ∈ R, p i)) - (a y : ZMod (∏ i ∈ R, p i))) =
        ∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)),
          ZMod.stdAddChar (h * ((a x : ZMod (p i)) - (a y : ZMod (p i)))) := by
    simpa only [Int.cast_sub] using unitRamanujanKernel_subset p R hc (a x - a y)
  simp_rw [hk]
  rw [tensorRamanujan_energy_expansion p S R A (fun x i => (a x : ZMod (p i))) ha]
  simp only [subsetSieveCoefficient, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_one, mul_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSubsetSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the positive subset expansion inside the additive large sieve -/

namespace Ostmann
open scoped Classical BigOperators

theorem prime_subset_product_dvd_iff {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (R : Finset (Fin n)) (i : Fin n) : (p i ∣ ∏ j ∈ R, p j) ↔ i ∈ R := by
  rw [(Fact.out : (p i).Prime).prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨j, hj, hd⟩
    by_cases hij : i = j
    · simpa only [hij] using hj
    · exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mp (hc hij) hd).elim
  · intro hi
    exact ⟨i, hi, dvd_rfl⟩

theorem prime_subset_product_injective {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Function.Injective (fun R : Finset (Fin n) => ∏ i ∈ R, p i) := by
  intro R T h
  ext i
  rw [← prime_subset_product_dvd_iff p hc R i,
    ← prime_subset_product_dvd_iff p hc T i]
  exact Iff.of_eq (congrArg (fun q => p i ∣ q) h)

/-- The complete double sum is bounded by the classical additive large sieve.
No centered-coordinate energy estimate is postulated in this step. -/
theorem prime_subset_sieve_bound (ls : PublishedAdditiveLargeSieve)
    {n M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (G : Finset (Finset (Fin n)))
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (hprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q)
    (ha : ∀ R ∈ G, ∀ x ∈ A, ∀ i ∈ R, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i) :
    (∑ R ∈ G, ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
      centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  have hpos (R : Finset (Fin n)) : 0 < ∏ i ∈ R, p i :=
    Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
  have he (R) (hR : R ∈ G) :
      (∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
        centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) =
      intervalSetReducedEnergy A J (∏ i ∈ R, p i) := by
    let : NeZero (∏ i ∈ R, p i) := ⟨(hpos R).ne'⟩
    rw [intervalSetReducedEnergy_eq_unitFrequencyEnergy]
    exact (subset_reduced_energy_expansion p S R hc A
      (fun x => J + (x.val : ℤ)) (ha R hR)).symm
  calc
    _ = ∑ R ∈ G, intervalSetReducedEnergy A J (∏ i ∈ R, p i) :=
      Finset.sum_congr rfl he
    _ = ∑ q ∈ G.image (fun R => ∏ i ∈ R, p i), intervalSetReducedEnergy A J q := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => prime_subset_product_injective p hc h
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy A J q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_Icc.mpr ⟨hpos R, hprod R hR⟩
      · intro q _ _
        exact intervalSetReducedEnergy_nonneg A J q
    _ ≤ _ := additiveSieve_probability_bound ls hM hQ A hA J

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensPrimeBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact published Mertens input for logarithmic prime bands

F. Mertens, J. reine angew. Math. 78 (1874), 46–62, first theorem,
DOI 10.1515/crll.1874.78.46. Both sides of the bounded-error estimate
are needed to subtract the lower cutoff; the collision argument uses
only its previously recorded lower-bound consequence.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem MertensEstimate.upper {C : ℝ} (h : MertensEstimate C) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) ≤ Real.log Q + C := by
  have hh := (abs_le.mp (h Q hQ)).2
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensFromFirst
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded second Mertens estimate from the first

Only bounded error is needed in the Ostmann application. Partial summation
therefore makes the second prime-sum input a consequence of the first.
-/

namespace Ostmann

open Finset MeasureTheory
open scoped BigOperators Interval

theorem MertensEstimate.floor_error {C : ℝ} (hM : MertensEstimate C)
    {t : ℝ} (ht : 2 ≤ t) :
    |(∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t| ≤
      C + Real.log 2 := by
  have hf : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hf0 : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (show 0 < ⌊t⌋₊ by omega)
  have ht0 : 0 < t := by linarith
  have hhalf : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor t
    linarith
  have hlo := Real.log_le_log (show 0 < t / 2 by positivity) hhalf
  rw [Real.log_div ht0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlo
  have hhi := Real.log_le_log hf0 (Nat.floor_le ht0.le)
  have hM' := abs_le.mp (hM _ hf)
  rw [abs_le]
  constructor <;> linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]

private theorem sum_logPrimeCoefficient (Q : ℕ) :
    (∑ n ∈ Icc 0 Q, logPrimeCoefficient n) =
      ∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p := by
  rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  rfl

private theorem sum_inv_log_mul_logPrimeCoefficient (Q : ℕ) :
    (∑ n ∈ Icc 0 Q, (Real.log (n : ℝ))⁻¹ * logPrimeCoefficient n) =
      ∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹ := by
  rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp only [logPrimeCoefficient, hp, ↓reduceIte]
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    field_simp
  · simp [logPrimeCoefficient, hp]

private theorem inv_log_differentiable {t : ℝ} (ht : 1 < t) :
    DifferentiableAt ℝ (fun x : ℝ => (Real.log x)⁻¹) t := by
  exact (Real.differentiableAt_log (by linarith)).inv (Real.log_pos ht).ne'

private theorem inv_log_deriv_continuous (Q : ℕ) :
    ContinuousOn (deriv (fun x : ℝ => (Real.log x)⁻¹)) (Set.Icc 2 Q) := by
  simp only [Real.deriv_inv_log]
  fun_prop (disch := grind [Real.log_pos, ne_of_gt])

/-- Partial summation for precisely the two prime weights used downstream. -/
theorem prime_reciprocal_partial_summation (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹) =
      (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) / Real.log Q +
      ∫ t in (2 : ℝ)..Q,
        (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
          (t⁻¹ / Real.log t ^ 2) := by
  have hid := sum_mul_eq_sub_integral_mul₁ logPrimeCoefficient
    (by norm_num [logPrimeCoefficient]) (by norm_num [logPrimeCoefficient]) (Q : ℝ)
    (f := fun x : ℝ => (Real.log x)⁻¹)
    (fun t ht => inv_log_differentiable (by linarith [ht.1]))
    (inv_log_deriv_continuous Q).integrableOn_Icc
  rw [Nat.floor_natCast, sum_inv_log_mul_logPrimeCoefficient,
    sum_logPrimeCoefficient] at hid
  simp_rw [Real.deriv_inv_log, sum_logPrimeCoefficient] at hid
  rw [← intervalIntegral.integral_of_le (show (2 : ℝ) ≤ Q by exact_mod_cast hQ)] at hid
  have hfun : (fun t : ℝ => -t⁻¹ / Real.log t ^ 2 *
      ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) =
      fun t : ℝ => -((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
        (t⁻¹ / Real.log t ^ 2)) := by
    funext t
    ring
  rw [hfun, intervalIntegral.integral_neg] at hid
  simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using hid

private theorem mertens_kernel_continuous (Q : ℕ) :
    ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t ^ 2) (Set.Icc 2 Q) := by
  fun_prop (disch := grind [Real.log_pos, ne_of_gt])

private theorem mertens_weighted_sum_integrable (Q : ℕ) (hQ : 2 ≤ Q) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
        (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le
    (show (2 : ℝ) ≤ Q by exact_mod_cast hQ)]
  have h := integrableOn_mul_sum_Icc logPrimeCoefficient (m := 0)
    (show (0 : ℝ) ≤ 2 by norm_num) (mertens_kernel_continuous Q).integrableOn_Icc
  simpa only [sum_logPrimeCoefficient, mul_comm] using h

private theorem mertens_log_kernel_continuous (Q : ℕ) :
    ContinuousOn (fun t : ℝ => Real.log t * (t⁻¹ / Real.log t ^ 2))
      (Set.Icc 2 Q) := by
  fun_prop (disch := grind [Real.log_pos, ne_of_gt])

private theorem mertens_log_kernel_integral (Q : ℕ) (hQ : 2 ≤ Q) :
    (∫ t in (2 : ℝ)..Q, Real.log t * (t⁻¹ / Real.log t ^ 2)) =
      Real.log (Real.log Q) - Real.log (Real.log 2) := by
  rw [← integral_inv_div_log (by norm_num : (1 : ℝ) < 2)
    (show (1 : ℝ) < Q by exact_mod_cast (show 1 < Q by omega))]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht2 : 2 ≤ t := (Set.uIcc_of_le
    (show (2 : ℝ) ≤ Q by exact_mod_cast hQ) ▸ ht).1
  have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
  field_simp

private theorem mertens_error_integral_bound {C : ℝ} (hM : MertensEstimate C)
    (Q : ℕ) (hQ : 2 ≤ Q) :
    |∫ t in (2 : ℝ)..Q,
      ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
        (t⁻¹ / Real.log t ^ 2)| ≤ (C + Real.log 2) / Real.log 2 := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hM 1 le_rfl)
  have hD : 0 ≤ C + Real.log 2 := add_nonneg hC (Real.log_nonneg (by norm_num))
  have hk : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t ^ 2) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    exact (mertens_kernel_continuous Q).integrableOn_Icc
  have hl : IntervalIntegrable (fun t : ℝ => Real.log t *
      (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    exact (mertens_log_kernel_continuous Q).integrableOn_Icc
  have he : IntervalIntegrable (fun t : ℝ =>
      ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
        (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
    simpa only [sub_mul] using (mertens_weighted_sum_integrable Q hQ).sub hl
  calc
    _ ≤ ∫ t in (2 : ℝ)..Q,
        |((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
          (t⁻¹ / Real.log t ^ 2)| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm hQR (f := fun t : ℝ =>
          ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
            (t⁻¹ / Real.log t ^ 2)))
    _ ≤ ∫ t in (2 : ℝ)..Q, (C + Real.log 2) * (t⁻¹ / Real.log t ^ 2) := by
      apply intervalIntegral.integral_mono_on hQR he.norm (hk.const_mul _)
      intro t ht
      have hk0 : 0 ≤ t⁻¹ / Real.log t ^ 2 :=
        div_nonneg (inv_nonneg.mpr (by linarith [ht.1])) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
      exact mul_le_mul_of_nonneg_right (hM.floor_error ht.1) hk0
    _ = (C + Real.log 2) * ((Real.log 2)⁻¹ - (Real.log Q)⁻¹) := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_div_log_sq (by norm_num : (1 : ℝ) < 2)
          (show (1 : ℝ) < Q by exact_mod_cast (show 1 < Q by omega))]
    _ ≤ (C + Real.log 2) / Real.log 2 := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ hD
      have : 0 ≤ (Real.log (Q : ℝ))⁻¹ :=
        inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega)))
      linarith

/-- The bounded-error second theorem follows from the first; no second
independent Mertens hypothesis is needed by the conditional main theorem. -/
theorem MertensEstimate.harmonic {C : ℝ} (hM : MertensEstimate C) :
    MertensHarmonicEstimate
      (|1 - Real.log (Real.log 2)| + (2 * C + Real.log 2) / Real.log 2) := by
  intro Q hQ
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hlogle : Real.log 2 ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by norm_num) hQR
  have hC : 0 ≤ C := (abs_nonneg _).trans (hM 1 le_rfl)
  have hl : IntervalIntegrable (fun t : ℝ => Real.log t *
      (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    exact (mertens_log_kernel_continuous Q).integrableOn_Icc
  have hei : (∫ t in (2 : ℝ)..Q,
      ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
        (t⁻¹ / Real.log t ^ 2)) =
      (∫ t in (2 : ℝ)..Q,
        (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
          (t⁻¹ / Real.log t ^ 2)) -
        (Real.log (Real.log Q) - Real.log (Real.log 2)) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (mertens_weighted_sum_integrable Q hQ) hl,
      mertens_log_kernel_integral Q hQ]
  have hid : (∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹) - Real.log (Real.log Q) =
      (1 - Real.log (Real.log 2)) +
        ((∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) - Real.log Q) / Real.log Q +
        (∫ t in (2 : ℝ)..Q,
          ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
            (t⁻¹ / Real.log t ^ 2)) := by
    rw [hei, prime_reciprocal_partial_summation Q hQ]
    field_simp
    ring
  have hendpoint : |((∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) -
      Real.log Q) / Real.log Q| ≤ C / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogQ]
    exact (div_le_div_of_nonneg_right (hM Q (by omega)) hlogQ.le).trans
      (div_le_div_of_nonneg_left hC hlog2 hlogle)
  rw [hid]
  calc
    _ ≤ |1 - Real.log (Real.log 2)| +
        |((∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) - Real.log Q) / Real.log Q| +
        |∫ t in (2 : ℝ)..Q,
          ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
            (t⁻¹ / Real.log t ^ 2)| := (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |1 - Real.log (Real.log 2)| + C / Real.log 2 +
        (C + Real.log 2) / Real.log 2 := by
      exact add_le_add (add_le_add le_rfl hendpoint)
        (mertens_error_integral_bound hM Q hQ)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ProgressionPrincipalPNT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor-one consequence of the progression input

The principal smooth PNT is not an independent input: the conductor-one
theta estimate, elementary prime-power removal and partial summation suffice.
-/

namespace Ostmann

open Filter
open scoped Classical BigOperators

theorem primeProgressionTheta_one (x : ℝ) :
    primeProgressionTheta 1 0 x = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp [primeProgressionTheta, primeProgressionLog, Finset.sum_filter, Nat.ModEq, Nat.mod_one]

theorem PublishedProgressionInput.principal_theta_bound (P : PublishedProgressionInput)
    (x : ℝ) (hx : 2 ≤ x) :
    |Chebyshev.theta x - x| ≤
      P.errorConstant * x * Real.exp (-P.decay * Real.sqrt (Real.log x)) := by
  have h := P.theta 1 le_rfl 0 (by norm_num) x hx
  simpa only [primeProgressionTheta_one, P.localZero_one, pageCoefficient, pageBeta,
    Nat.totient_one, Nat.cast_one, thetaMainTerm, zero_mul, zero_div, sub_zero, div_one]
    using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensThetaKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the conductor-one theta error

The exponential square-root error has a bounded logarithmic integral. This
concrete antiderivative suffices for the first Mertens estimate.
-/

namespace Ostmann

open MeasureTheory
open scoped Interval

theorem hasDerivAt_thetaErrorPrimitive {c t : ℝ} (hc : 0 < c) (ht : 1 < t) :
    HasDerivAt (thetaErrorPrimitive c)
      (Real.exp (-c * Real.sqrt (Real.log t)) / t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hs0 : Real.sqrt (Real.log t) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  have hs := (Real.hasDerivAt_sqrt hlog.ne').comp t (Real.hasDerivAt_log ht0)
  have hl := ((hs.const_mul c).add_const 1).const_mul (-(2 / c ^ 2))
  have hr := (hs.const_mul (-c)).exp
  refine (hl.mul hr).congr_deriv ?_
  · simp only [Function.comp_apply]
    field_simp
    ring

theorem thetaErrorPrimitive_nonpos {c : ℝ} (hc : 0 < c) (t : ℝ) :
    thetaErrorPrimitive c t ≤ 0 := by
  unfold thetaErrorPrimitive
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity))
    (Real.exp_nonneg _)

/-- A uniform bound independent of the upper cutoff. -/
theorem theta_error_kernel_integral_bound {c X : ℝ} (hc : 0 < c) (hX : 2 ≤ X) :
    (∫ t in (2 : ℝ)..X, Real.exp (-c * Real.sqrt (Real.log t)) / t) ≤
      -thetaErrorPrimitive c 2 := by
  have hi : IntervalIntegrable (fun t : ℝ =>
      Real.exp (-c * Real.sqrt (Real.log t)) / t) volume 2 X := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX]
    apply ContinuousOn.integrableOn_Icc
    fun_prop (disch := grind)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht =>
    hasDerivAt_thetaErrorPrimitive hc (by
      rw [Set.uIcc_of_le hX] at ht
      linarith [ht.1])) hi]
  linarith [thetaErrorPrimitive_nonpos hc X]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_MertensFromProgression
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens estimates from the progression estimate

The conductor-one theta bound implies the first Mertens estimate.
-/

namespace Ostmann

open Finset MeasureTheory
open scoped BigOperators Interval

/-- Abel summation for the logarithmically weighted prime sum. -/
theorem prime_log_div_partial_summation (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) =
      Chebyshev.theta Q / Q + ∫ t in (2 : ℝ)..Q, Chebyshev.theta t / t ^ 2 := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd : ContinuousOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc 2 Q) := by
    simp only [deriv_inv']
    exact ((continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))).neg
  have h := sum_mul_eq_sub_integral_mul₁ (primeProgressionLog 1 0)
    (by norm_num [primeProgressionLog]) (by norm_num [primeProgressionLog]) (Q : ℝ)
    (f := fun t : ℝ => t⁻¹)
    (fun t ht => (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).differentiableAt)
    hd.integrableOn_Icc
  have hs : (∑ n ∈ Icc 0 Q, (n : ℝ)⁻¹ * primeProgressionLog 1 0 n) =
      ∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p := by
    rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
    apply sum_congr rfl
    intro n hn
    simp [primeProgressionLog, Nat.ModEq, Nat.mod_one, mul_ite, div_eq_mul_inv, mul_comm]
  change _ = (Q : ℝ)⁻¹ * primeProgressionTheta 1 0 Q -
    ∫ t in Set.Ioc (2 : ℝ) Q, deriv (fun t : ℝ => t⁻¹) t *
      primeProgressionTheta 1 0 t at h
  rw [Nat.floor_natCast, hs] at h
  simp_rw [primeProgressionTheta_one, deriv_inv, neg_mul] at h
  rw [← intervalIntegral.integral_of_le hQR, intervalIntegral.integral_neg,
    sub_neg_eq_add] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

private theorem theta_div_sq_integrable (Q : ℕ) (hQ : 2 ≤ Q) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / t ^ 2) volume 2 Q := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le
    (show (2 : ℝ) ≤ Q by exact_mod_cast hQ)]
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc 2 Q) := by
    exact (continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
  have h := integrableOn_mul_sum_Icc (primeProgressionLog 1 0)
    (m := 0) (show (0 : ℝ) ≤ 2 by norm_num) hc.integrableOn_Icc
  change IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹ * primeProgressionTheta 1 0 t)
    (Set.Icc 2 Q) at h
  simpa only [primeProgressionTheta_one, div_eq_mul_inv, mul_comm] using h

/-- The integrated theta error is bounded independently of the cutoff. -/
theorem PublishedProgressionInput.theta_error_integral (P : PublishedProgressionInput)
    (Q : ℕ) (hQ : 2 ≤ Q) :
    |∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2| ≤
      P.errorConstant * (-thetaErrorPrimitive P.decay 2) := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hk : IntervalIntegrable (fun t : ℝ =>
      Real.exp (-P.decay * Real.sqrt (Real.log t)) / t) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    apply ContinuousOn.integrableOn_Icc
    fun_prop (disch := grind)
  have hi : IntervalIntegrable (fun t : ℝ =>
      (Chebyshev.theta t - t) / t ^ 2) volume 2 Q := by
    have hv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 2 Q := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
      apply ContinuousOn.integrableOn_Icc
      fun_prop (disch := grind)
    apply ((theta_div_sq_integrable Q hQ).sub hv).congr
    intro t ht
    rw [Set.uIoc_of_le hQR] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    field_simp
  calc
    _ ≤ ∫ t in (2 : ℝ)..Q, |(Chebyshev.theta t - t) / t ^ 2| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm hQR
          (f := fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2))
    _ ≤ ∫ t in (2 : ℝ)..Q,
        P.errorConstant * (Real.exp (-P.decay * Real.sqrt (Real.log t)) / t) := by
      apply intervalIntegral.integral_mono_on hQR hi.norm (hk.const_mul _)
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      calc
        _ ≤ (P.errorConstant * t * Real.exp (-P.decay * Real.sqrt (Real.log t))) /
            t ^ 2 := div_le_div_of_nonneg_right (P.principal_theta_bound t ht.1)
              (sq_nonneg _)
        _ = _ := by field_simp
    _ = P.errorConstant * ∫ t in (2 : ℝ)..Q,
        Real.exp (-P.decay * Real.sqrt (Real.log t)) / t :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (theta_error_kernel_integral_bound P.decay_pos hQR) P.errorConstant_nonneg

theorem PublishedProgressionInput.mertensConstant_nonneg (P : PublishedProgressionInput) :
    0 ≤ P.mertensConstant := by
  unfold PublishedProgressionInput.mertensConstant
  exact add_nonneg (add_nonneg (abs_nonneg _) P.errorConstant_nonneg)
    (mul_nonneg P.errorConstant_nonneg (neg_nonneg.mpr
      (thetaErrorPrimitive_nonpos P.decay_pos 2)))

/-- First Mertens, with a concrete constant depending on the
progression estimate. -/
theorem PublishedProgressionInput.mertens (P : PublishedProgressionInput) :
    MertensEstimate P.mertensConstant := by
  intro Q hQ
  by_cases hQ2 : 2 ≤ Q
  · have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
    have hQ0 : (0 : ℝ) < Q := by linarith
    have hv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 2 Q := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
      apply ContinuousOn.integrableOn_Icc
      fun_prop (disch := grind)
    have hsplit : (∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2) =
        (∫ t in (2 : ℝ)..Q, Chebyshev.theta t / t ^ 2) -
          (Real.log Q - Real.log 2) := by
      have he : (∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2) =
          ∫ t in (2 : ℝ)..Q, Chebyshev.theta t / t ^ 2 - t⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hQR] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        field_simp
      rw [he, intervalIntegral.integral_sub (theta_div_sq_integrable Q hQ2) hv,
        integral_inv_of_pos (by norm_num) hQ0,
        Real.log_div hQ0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have hid : (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) - Real.log Q =
        (1 - Real.log 2) + (Chebyshev.theta Q - Q) / Q +
          ∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2 := by
      rw [hsplit, prime_log_div_partial_summation Q hQ2]
      field_simp
      ring
    have hend : |(Chebyshev.theta Q - Q) / Q| ≤ P.errorConstant := by
      rw [abs_div, abs_of_pos hQ0]
      calc
        _ ≤ (P.errorConstant * Q * Real.exp (-P.decay * Real.sqrt (Real.log Q))) / Q :=
          div_le_div_of_nonneg_right (P.principal_theta_bound Q hQR) hQ0.le
        _ = P.errorConstant * Real.exp (-P.decay * Real.sqrt (Real.log Q)) := by
          field_simp
        _ ≤ P.errorConstant * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr P.decay_pos.le) (Real.sqrt_nonneg _))) P.errorConstant_nonneg
        _ = _ := mul_one _
    rw [hid]
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add le_rfl hend) (P.theta_error_integral Q hQ2))
  · have hQ1 : Q = 1 := by omega
    subst Q
    simpa only [Nat.primesLE_one, sum_empty, Nat.cast_one, Real.log_one, sub_self,
      abs_zero] using P.mertensConstant_nonneg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandSizePrimeBand
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary dyadic prime counts used in the summand-size argument -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem actual_theta_relative_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ ε * x := by
  let P := actualProgressionInput
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 P.decay P.decay_pos).comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  simp only [Real.rpow_zero, one_mul, Function.comp_def] at ht
  have hCt := ht.const_mul P.errorConstant
  rw [mul_zero] at hCt
  have hsmall := hCt.eventually_lt_const hε
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x he hx
  have hbound := P.principal_theta_bound x hx
  have hm := mul_le_mul_of_nonneg_right he.le (by linarith : 0 ≤ x)
  nlinarith

 theorem mem_sizePrimeBand {Q p : ℕ} :
    p ∈ sizePrimeBand Q ↔ p.Prime ∧ Q < p ∧ p ≤ 2 * Q := by
  simp only [sizePrimeBand, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hle, hp⟩, hnot⟩
    have hn : ¬ p ≤ Q := fun hh => hnot ⟨hh, hp⟩
    exact ⟨hp, by omega, hle⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨hhi, hp⟩, by omega⟩

 theorem sizePrimeBand_log_sum (Q : ℕ) :
    (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) =
      Chebyshev.theta (2 * Q : ℕ) - Chebyshev.theta Q := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have hsub : Nat.primesLE Q ⊆ Nat.primesLE (2 * Q) := by
    intro p hp
    obtain ⟨hpQ, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩
  simpa only [sizePrimeBand] using
    eq_sub_of_add_eq (Finset.sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hsub)

 theorem sizePrimeBand_eventual_bounds :
    ∀ᶠ Q : ℕ in atTop, 2 ≤ Q ∧
      (Q : ℝ) / (4 * Real.log (2 * Q)) ≤ (sizePrimeBand Q).card ∧
      (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) ≤ 3 * Q := by
  have ht := actual_theta_relative_small (by norm_num : (0 : ℝ) < 1 / 4)
  have htN := tendsto_natCast_atTop_atTop.eventually ht
  obtain ⟨N, hN⟩ := eventually_atTop.mp htN
  filter_upwards [eventually_ge_atTop (max N 2)] with Q hQ
  have hQ2 : 2 ≤ Q := (le_max_right _ _).trans hQ
  have hQN : N ≤ Q := (le_max_left _ _).trans hQ
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have h1 := hN Q hQN
  have h2 := hN (2 * Q) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h2
  have hmass : (Q : ℝ) / 4 ≤ ∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ) := by
    rw [sizePrimeBand_log_sum]
    push_cast
    rw [abs_le] at h1 h2
    nlinarith
  have hupper : (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) ≤ 3 * Q := by
    rw [sizePrimeBand_log_sum]
    push_cast
    rw [abs_le] at h1 h2
    nlinarith
  have hcount : (∑ p ∈ sizePrimeBand Q, Real.log (p : ℝ)) ≤
      (sizePrimeBand Q).card * Real.log (2 * Q) := by
    calc
      _ ≤ ∑ _p ∈ sizePrimeBand Q, Real.log (2 * (Q : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hmem := mem_sizePrimeBand.mp hp
        exact Real.log_le_log (by exact_mod_cast hmem.1.pos) (by exact_mod_cast hmem.2.2)
      _ = _ := by simp
  have hl : 0 < Real.log (2 * (Q : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * Q))
  refine ⟨hQ2, ?_, hupper⟩
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log (2 * (Q : ℝ)))).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandCoverageLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counting lower bound from prime coverage -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem EventuallyPrimeSumset.prime_coverage_card {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N₀ : ℕ, ∀ N : ℕ,
      (Nat.primesLE N).card ≤ N₀ + (summandPrefix A N).card * (summandPrefix B N).card := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨N₀, ?_⟩
  intro N
  let U := (Nat.primesLE N).filter fun p => N₀ ≤ p
  let V := (Nat.primesLE N).filter fun p => ¬ N₀ ≤ p
  have hV : V.card ≤ N₀ := by
    have hsub : V ⊆ Finset.range N₀ := by
      intro p hp
      exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hp).2; omega)
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hU : U.card ≤ (summandPrefix A N).card * (summandPrefix B N).card := by
    have hsub : U ⊆ ((summandPrefix A N) ×ˢ (summandPrefix B N)).image (fun ab => ab.1 + ab.2) := by
      intro p hp
      obtain ⟨hpN, hpprime⟩ := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
      obtain ⟨a, ha, b, hb, hab⟩ :=
        mem_sumset.mp ((hN p (Finset.mem_filter.mp hp).2).mpr hpprime)
      refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨?_, ?_⟩, hab⟩
      · exact (mem_summandPrefix A N a).mpr ⟨ha, by omega⟩
      · exact (mem_summandPrefix B N b).mpr ⟨hb, by omega⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans_eq (Finset.card_product _ _))
  have hsplit := Finset.card_filter_add_card_filter_not (s := Nat.primesLE N) (fun p => N₀ ≤ p)
  change U.card + V.card = (Nat.primesLE N).card at hsplit
  omega

 theorem EventuallyPrimeSumset.coverage_product_lower {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) / (4 * Real.log (N : ℝ)) ≤
      ((summandPrefix A N).card : ℝ) * (summandPrefix B N).card := by
  obtain ⟨N₀, hcoverage⟩ := h.prime_coverage_card
  have htheta := tendsto_natCast_atTop_atTop.eventually
    (actual_theta_relative_small (by norm_num : (0 : ℝ) < 1 / 2))
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).const_mul_left
    (N₀ : ℝ)).bound (by norm_num : (0 : ℝ) < 1 / 4)
  have hsmallN := tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [htheta, hsmallN, eventually_ge_atTop (2 : ℕ)] with N hθ hs hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hNp : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have herr : (N₀ : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) / 4 := by
    simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hNp,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N₀) hlog.le), one_div, div_eq_mul_inv, one_mul, mul_comm] using hs
  have hsum : Chebyshev.theta (N : ℝ) ≤ (Nat.primesLE N).card * Real.log (N : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      _ ≤ ∑ _p ∈ Nat.primesLE N, Real.log (N : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos)
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).1)
      _ = _ := by simp
  have hc : ((Nat.primesLE N).card : ℝ) ≤ N₀ +
      ((summandPrefix A N).card : ℝ) * (summandPrefix B N).card := by exact_mod_cast hcoverage N
  have hmul := mul_le_mul_of_nonneg_right hc hlog.le
  rw [abs_le] at hθ
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log (N : ℝ))).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftInitialSegment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoring the removed initial interval in fixed-shift sieving -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem summandPrefix_card_le_initial_add_tail (C : Set ℕ) (lo N : ℕ) :
    (summandPrefix C N).card ≤ lo + 1 + (summandTail C lo N).card := by
  have hsub : summandPrefix C N ⊆ Finset.range (lo + 1) ∪ summandTail C lo N := by
    intro a ha
    obtain ⟨haC, haN⟩ := mem_summandPrefix C N a |>.mp ha
    by_cases hlo : a ≤ lo
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    · exact Finset.mem_union_right _ (mem_summandTail C lo N a |>.mpr ⟨haC, by omega, haN⟩)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa only [Finset.card_range] using hh

 theorem sqrt_log_power_initial_small (j : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, (Real.sqrt x + C + 1) * Real.log x ^ j ≤ x := by
  have hc : 0 < 1 / (C + 2) := by positivity
  have hbound := (isLittleO_log_rpow_rpow_atTop (j : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).bound hc
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hr : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by simpa using hx1)
  have hp : 0 ≤ Real.log x ^ j := pow_nonneg hl _
  rw [Real.rpow_natCast, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hp, abs_of_nonneg (Real.sqrt_nonneg x)] at hx
  have hlog : Real.log x ^ j ≤ Real.sqrt x / (C + 2) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hx
  have hm : (C + 2) * Real.log x ^ j ≤ Real.sqrt x := by
    have hh := (le_div_iff₀ (by positivity : 0 < C + 2)).mp hlog
    nlinarith
  have hs : Real.sqrt x + C + 1 ≤ (C + 2) * Real.sqrt x := by nlinarith
  calc
    _ ≤ ((C + 2) * Real.sqrt x) * Real.log x ^ j := mul_le_mul_of_nonneg_right hs hp
    _ = Real.sqrt x * ((C + 2) * Real.log x ^ j) := by ring
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg x)
    _ = x := by nlinarith [Real.sq_sqrt hx0]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SieveWeightMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Euler-weight moment needed for fixed-shift sieving -/

namespace Ostmann

open scoped Classical BigOperators

 theorem sieve_weight_mass (P : Finset ℕ) (w : ℕ → ℝ) :
    (∑ U ∈ P.powerset, ∏ p ∈ U, w p) = ∏ p ∈ P, (1 + w p) :=
  (Finset.prod_one_add P).symm

 theorem sieve_weight_moment (P : Finset ℕ) (w L : ℕ → ℝ)
    (hw : ∀ p ∈ P, 1 + w p ≠ 0) :
    (∑ U ∈ P.powerset, (∏ p ∈ U, w p) * ∑ p ∈ U, L p) =
      (∏ p ∈ P, (1 + w p)) * ∑ p ∈ P, (w p / (1 + w p)) * L p := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hfresh (U : Finset ℕ) (hU : U ∈ P.powerset) : p ∉ U :=
      fun h => hp (Finset.mem_powerset.mp hU h)
    have hwP : ∀ q ∈ P, 1 + w q ≠ 0 := fun q hq => hw q (Finset.mem_insert_of_mem hq)
    have hwp : 1 + w p ≠ 0 := hw p (Finset.mem_insert_self _ _)
    have hsecond :
        (∑ U ∈ P.powerset, (∏ q ∈ insert p U, w q) * ∑ q ∈ insert p U, L q) =
          w p * (L p * (∏ q ∈ P, (1 + w q)) +
            ∑ U ∈ P.powerset, (∏ q ∈ U, w q) * ∑ q ∈ U, L q) := by
      calc
        _ = ∑ U ∈ P.powerset,
            w p * (L p * (∏ q ∈ U, w q) + (∏ q ∈ U, w q) * ∑ q ∈ U, L q) := by
          apply Finset.sum_congr rfl
          intro U hU
          rw [Finset.prod_insert (hfresh U hU), Finset.sum_insert (hfresh U hU)]
          ring
        _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, sieve_weight_mass]
    rw [Finset.sum_powerset_insert hp, hsecond, ih hwP, Finset.prod_insert hp,
      Finset.sum_insert hp]
    field_simp [hwp]
    ring

 theorem fixed_shift_weight_moment (P : Finset ℕ) (j : ℝ)
    (hj : 0 ≤ j) (hP : ∀ p ∈ P, j < (p : ℝ)) :
    (∑ U ∈ P.powerset, (∏ p ∈ U, j / ((p : ℝ) - j)) * ∑ p ∈ U, Real.log (p : ℝ)) =
      (∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j)) *
        (j * ∑ p ∈ P, Real.log (p : ℝ) / p) := by
  have hfactor (p : ℕ) (hp : p ∈ P) : 1 + j / ((p : ℝ) - j) = (p : ℝ) / ((p : ℝ) - j) := by
    have hn : (p : ℝ) - j ≠ 0 := ne_of_gt (sub_pos.mpr (hP p hp))
    field_simp [hn]
    ring
  have hprob (p : ℕ) (hp : p ∈ P) :
      (j / ((p : ℝ) - j)) / (1 + j / ((p : ℝ) - j)) = j / p := by
    rw [hfactor p hp]
    have hn : (p : ℝ) - j ≠ 0 := ne_of_gt (sub_pos.mpr (hP p hp))
    have hnp : (p : ℝ) ≠ 0 := ne_of_gt (lt_of_le_of_lt hj (hP p hp))
    field_simp
  rw [sieve_weight_moment P _ _ (fun p hp => by
    rw [hfactor p hp]
    exact (div_pos (lt_of_le_of_lt hj (hP p hp)) (sub_pos.mpr (hP p hp))).ne')]
  rw [Finset.prod_congr rfl hfactor]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hprob p hp]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SieveWeightTruncation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining short squarefree products in the fixed-shift sieve -/

namespace Ostmann

open scoped Classical BigOperators

 theorem finite_weight_truncation {ι : Type*} (S : Finset ι) (w cost : ι → ℝ)
    (L : ℝ) (hL : 0 < L) (hw : ∀ s ∈ S, 0 ≤ w s) (hc : ∀ s ∈ S, 0 ≤ cost s)
    (hmean : (∑ s ∈ S, w s * cost s) ≤ (L / 2) * ∑ s ∈ S, w s) :
    (∑ s ∈ S, w s) / 2 ≤ ∑ s ∈ S.filter (fun s => cost s ≤ L), w s := by
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun s => cost s ≤ L) w
  have hbad : L * (∑ s ∈ S.filter (fun s => ¬ cost s ≤ L), w s) ≤
      ∑ s ∈ S, w s * cost s := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ s ∈ S.filter (fun s => ¬ cost s ≤ L), w s * cost s := by
        apply Finset.sum_le_sum
        intro s hs
        have hs' := Finset.mem_filter.mp hs
        have hlt : L < cost s := lt_of_not_ge hs'.2
        nlinarith [hw s hs'.1]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun s hs _ => mul_nonneg (hw s hs) (hc s hs))
  nlinarith

 theorem fixed_shift_short_weight (P : Finset ℕ) (j Q : ℝ)
    (hj : 0 ≤ j) (hQ : 1 < Q) (hP : ∀ p ∈ P, j < (p : ℝ))
    (hmean : j * (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ Real.log Q / 2) :
    ((∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j)) / 2) ≤
      ∑ U ∈ P.powerset.filter (fun U : Finset ℕ => (∑ p ∈ U, Real.log (p : ℝ)) ≤ Real.log Q),
        ∏ p ∈ U, j / ((p : ℝ) - j) := by
  have hfactor (p : ℕ) (hp : p ∈ P) :
      1 + j / ((p : ℝ) - j) = (p : ℝ) / ((p : ℝ) - j) := by
    have hn : (p : ℝ) - j ≠ 0 := ne_of_gt (sub_pos.mpr (hP p hp))
    field_simp [hn]
    ring
  have hmass : (∑ U ∈ P.powerset, ∏ p ∈ U, j / ((p : ℝ) - j)) =
      ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j) := by
    rw [sieve_weight_mass]
    exact Finset.prod_congr rfl hfactor
  have hweight (U : Finset ℕ) (hU : U ∈ P.powerset) :
      0 ≤ ∏ p ∈ U, j / ((p : ℝ) - j) := by
    exact Finset.prod_nonneg (fun p hp => div_nonneg hj
      (sub_pos.mpr (hP p (Finset.mem_powerset.mp hU hp))).le)
  have hcost (U : Finset ℕ) (hU : U ∈ P.powerset) :
      0 ≤ ∑ p ∈ U, Real.log (p : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    have hp' : (0 : ℝ) < p := lt_of_le_of_lt hj (hP p (Finset.mem_powerset.mp hU hp))
    have hpN : 1 ≤ p := by
      have hpNat : 0 < p := by exact_mod_cast hp'
      omega
    exact Real.log_nonneg (by exact_mod_cast hpN)
  have hmass0 : 0 ≤ ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j) :=
    Finset.prod_nonneg (fun p hp => div_nonneg (Nat.cast_nonneg p) (sub_pos.mpr (hP p hp)).le)
  have hm : (∑ U ∈ P.powerset,
      (∏ p ∈ U, j / ((p : ℝ) - j)) * ∑ p ∈ U, Real.log (p : ℝ)) ≤
      (Real.log Q / 2) * ∑ U ∈ P.powerset, ∏ p ∈ U, j / ((p : ℝ) - j) := by
    rw [fixed_shift_weight_moment P j hj hP, hmass]
    nlinarith [mul_le_mul_of_nonneg_left hmean hmass0]
  have h := finite_weight_truncation P.powerset
    (fun U => ∏ p ∈ U, j / ((p : ℝ) - j)) (fun U => ∑ p ∈ U, Real.log (p : ℝ))
    (Real.log Q) (Real.log_pos hQ) hweight hcost hm
  rwa [hmass] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_BoundedSieveSubsets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained Euler weights lie at the original integer sieve level -/

namespace Ostmann

open scoped Classical BigOperators

 theorem sieve_subset_log_iff (U : Finset ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hU : ∀ p ∈ U, 0 < p) :
    (∑ p ∈ U, Real.log (p : ℝ)) ≤ Real.log (Q : ℝ) ↔ (∏ p ∈ U, p) ≤ Q := by
  have hprod : (0 : ℝ) < (∏ p ∈ U, p : ℕ) := by
    exact_mod_cast Finset.prod_pos hU
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have heq : (∑ p ∈ U, Real.log (p : ℝ)) = Real.log ((∏ p ∈ U, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    exact fun p hp => Nat.cast_ne_zero.mpr (hU p hp).ne'
  rw [heq, Real.log_le_log_iff hprod hQR]
  exact_mod_cast Iff.rfl

 theorem fixed_shift_bounded_weight (P : Finset ℕ) (j : ℝ) (Q : ℕ)
    (hj : 0 ≤ j) (hQ : 2 ≤ Q) (hP : ∀ p ∈ P, j < (p : ℝ))
    (hmean : j * (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ Real.log (Q : ℝ) / 2) :
    ((∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j)) / 2) ≤
      ∑ U ∈ boundedSieveSubsets P Q, ∏ p ∈ U, j / ((p : ℝ) - j) := by
  have hQpos : 0 < Q := by omega
  have hpos : ∀ p ∈ P, 0 < p := by
    intro p hp
    exact_mod_cast lt_of_le_of_lt hj (hP p hp)
  have hsets : P.powerset.filter (fun U : Finset ℕ =>
      (∑ p ∈ U, Real.log (p : ℝ)) ≤ Real.log (Q : ℝ)) = boundedSieveSubsets P Q := by
    ext U
    simp only [boundedSieveSubsets, Finset.mem_filter]
    apply and_congr_right
    intro hU
    exact sieve_subset_log_iff U Q hQpos (fun p hp => hpos p (Finset.mem_powerset.mp hU hp))
  have h := fixed_shift_short_weight P j Q hj (by exact_mod_cast hQ) hP hmean
  rwa [hsets] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftEulerLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Euler-product lower bound for fixed-shift sieving -/

namespace Ostmann

open scoped Classical BigOperators

 theorem fixed_shift_euler_lower (P : Finset ℕ) (j : ℝ) (hj : 0 ≤ j)
    (hP : ∀ p ∈ P, j < (p : ℝ)) :
    Real.exp (j * ∑ p ∈ P, 1 / (p : ℝ)) ≤
      ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j) := by
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p _
    exact (Real.exp_pos _).le
  · intro p hp
    have hp0 : (0 : ℝ) < p := lt_of_le_of_lt hj (hP p hp)
    have hdiff : 0 < (p : ℝ) - j := sub_pos.mpr (hP p hp)
    have hratio : 0 < (p : ℝ) / ((p : ℝ) - j) := div_pos hp0 hdiff
    have hlog := Real.one_sub_inv_le_log_of_pos hratio
    have hid : 1 - ((p : ℝ) / ((p : ℝ) - j))⁻¹ = j * (1 / (p : ℝ)) := by
      field_simp
      ring
    rw [hid] at hlog
    exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hratio)

 theorem fixed_shift_euler_log_lower (P : Finset ℕ) (j : ℕ) (R C : ℝ)
    (hR : 1 < R) (hP : ∀ p ∈ P, (j : ℝ) < p)
    (hH : Real.log (Real.log R) - C ≤ ∑ p ∈ P, 1 / (p : ℝ)) :
    Real.exp (-(j : ℝ) * C) * Real.log R ^ j ≤
      ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j) := by
  have hp : Real.log R ^ j = Real.exp ((j : ℝ) * Real.log (Real.log R)) := by
    rw [Real.exp_nat_mul, Real.exp_log (Real.log_pos hR)]
  rw [hp, ← Real.exp_add]
  have hmul := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg (α := ℝ) j)
  have he : -(j : ℝ) * C + (j : ℝ) * Real.log (Real.log R) =
      (j : ℝ) * (Real.log (Real.log R) - C) := by ring
  rw [he]
  exact (Real.exp_le_exp.mpr hmul).trans
    (fixed_shift_euler_lower P j (Nat.cast_nonneg j) hP)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftMertensWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens bounds for the actual fixed-shift Euler weights -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem mem_fixedShiftPrimeSet {p₀ R p : ℕ} :
    p ∈ fixedShiftPrimeSet p₀ R ↔ p.Prime ∧ p₀ < p ∧ p ≤ R := by
  simp only [fixedShiftPrimeSet, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpR, hp⟩, hnot⟩
    have hn : ¬ p ≤ p₀ := fun hh => hnot ⟨hh, hp⟩
    exact ⟨hp, by omega, hpR⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨hhi, hp⟩, by omega⟩

 theorem fixedShiftPrimeSet_harmonic_lower (p₀ : ℕ) :
    ∃ C : ℝ, ∀ R : ℕ, max 2 p₀ ≤ R →
      Real.log (Real.log (R : ℝ)) - C ≤
        ∑ p ∈ fixedShiftPrimeSet p₀ R, 1 / (p : ℝ) := by
  let D := |1 - Real.log (Real.log 2)| +
    (2 * actualProgressionInput.mertensConstant + Real.log 2) / Real.log 2
  have hH : MertensHarmonicEstimate D := actualProgressionInput.mertens.harmonic
  refine ⟨D + ∑ p ∈ Nat.primesLE p₀, 1 / (p : ℝ), ?_⟩
  intro R hR
  have hR2 : 2 ≤ R := (le_max_left _ _).trans hR
  have hpR : p₀ ≤ R := (le_max_right _ _).trans hR
  have hsub : Nat.primesLE p₀ ⊆ Nat.primesLE R := by
    intro p hp
    obtain ⟨hpp, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpp.trans hpR, hpprime⟩
  have hs := Finset.sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) hsub
  have hb := (abs_le.mp (hH R hR2)).1
  simp only [← one_div] at hb
  change (∑ p ∈ fixedShiftPrimeSet p₀ R, 1 / (p : ℝ)) +
    (∑ p ∈ Nat.primesLE p₀, 1 / (p : ℝ)) = _ at hs
  linarith

 theorem fixedShiftPrimeSet_log_upper (p₀ R : ℕ) (hR : 1 ≤ R) :
    (∑ p ∈ fixedShiftPrimeSet p₀ R, Real.log (p : ℝ) / p) ≤
      Real.log (R : ℝ) + actualProgressionInput.mertensConstant := by
  apply le_trans _ (actualProgressionInput.mertens.upper R hR)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
  intro p hp _
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
    (Nat.cast_nonneg p)

 theorem fixed_shift_euler_power_lower (p₀ j : ℕ) (hj : j ≤ p₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℕ, max 2 p₀ ≤ R →
      c * Real.log (R : ℝ) ^ j ≤
        ∏ p ∈ fixedShiftPrimeSet p₀ R, (p : ℝ) / ((p : ℝ) - j) := by
  obtain ⟨C, hC⟩ := fixedShiftPrimeSet_harmonic_lower p₀
  refine ⟨Real.exp (-(j : ℝ) * C), Real.exp_pos _, ?_⟩
  intro R hR
  apply fixed_shift_euler_log_lower _ j R C
  · exact_mod_cast (show 1 < R from lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hR))
  · intro p hp
    exact_mod_cast lt_of_le_of_lt hj (mem_fixedShiftPrimeSet.mp hp).2.1
  · exact hC R hR

 theorem fixed_shift_weight_at_power (p₀ j : ℕ) (hj : 1 ≤ j) (hjp : j ≤ p₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ R : ℕ in atTop,
      c * Real.log (R : ℝ) ^ j ≤
        ∑ U ∈ boundedSieveSubsets (fixedShiftPrimeSet p₀ R) (R ^ (10 * j)),
          ∏ p ∈ U, (j : ℝ) / ((p : ℝ) - j) := by
  obtain ⟨c, hc, hweight⟩ := fixed_shift_euler_power_lower p₀ j hjp
  refine ⟨c / 2, by positivity, ?_⟩
  have hlog : ∀ᶠ R : ℕ in atTop, actualProgressionInput.mertensConstant ≤ Real.log (R : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hlog, eventually_ge_atTop (max 2 p₀)] with R hlog hR
  have hR2 : 2 ≤ R := (le_max_left _ _).trans hR
  have hR1 : 1 ≤ R := by omega
  have hprod : ∀ p ∈ fixedShiftPrimeSet p₀ R, (j : ℝ) < p := by
    intro p hp
    exact_mod_cast lt_of_le_of_lt hjp (mem_fixedShiftPrimeSet.mp hp).2.1
  have hQ : 2 ≤ R ^ (10 * j) := by
    have he : 1 ≤ 10 * j := by omega
    exact hR2.trans (Nat.le_self_pow (by omega : 10 * j ≠ 0) R)
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR1)
  have hlogQ : Real.log (R ^ (10 * j) : ℕ) = (10 * (j : ℝ)) * Real.log R := by
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  have hmean : (j : ℝ) * (∑ p ∈ fixedShiftPrimeSet p₀ R, Real.log (p : ℝ) / p) ≤
      Real.log (R ^ (10 * j) : ℕ) / 2 := by
    have hu := mul_le_mul_of_nonneg_left (fixedShiftPrimeSet_log_upper p₀ R hR1)
      (Nat.cast_nonneg (α := ℝ) j)
    rw [hlogQ]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hlogR]
  have hb := fixed_shift_bounded_weight (fixedShiftPrimeSet p₀ R) j (R ^ (10 * j))
    (Nat.cast_nonneg j) hQ hprod hmean
  have hcR := hweight R hR
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_OccupiedResidueCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The larger-sieve bound for the full residue support of a summand

The support is taken from the entire infinite summand, even when the probability
measure is supported on one finite prefix. This is the upper bound for H in
manuscript Lemma 2.4 and Elsholtz's summand-size argument.
-/

namespace Ostmann

open scoped BigOperators Classical

 theorem mem_occupiedResidues {A : Set ℕ} {p r : ℕ} :
    r ∈ occupiedResidues A p ↔ r < p ∧ ∃ a ∈ A, a % p = r := by
  classical
  simp only [occupiedResidues, Finset.mem_filter, Finset.mem_range]

 theorem occupiedResidues_nonempty {A : Set ℕ} (hA : A.Nonempty) {p : ℕ}
    (hp : 0 < p) : (occupiedResidues A p).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a % p, mem_occupiedResidues.mpr ⟨Nat.mod_lt a hp, a, ha, rfl⟩⟩

 theorem uniformResidueCollision_support_lower (A : Set ℕ) (s : Finset ℕ)
    (hs : s.Nonempty) (hsA : ∀ a ∈ s, a ∈ A) {p : ℕ} (hp : 0 < p) :
    1 / ((occupiedResidues A p).card : ℝ) ≤ uniformResidueCollision s p := by
  classical
  have hA : A.Nonempty := by obtain ⟨a, ha⟩ := hs; exact ⟨a, hsA a ha⟩
  have hmap : ∀ a ∈ s, a % p ∈ occupiedResidues A p := by
    intro a ha
    exact mem_occupiedResidues.mpr ⟨Nat.mod_lt a hp, a, hsA a ha, rfl⟩
  have hmass : (∑ r ∈ occupiedResidues A p,
      fiberMass s (fun _ => 1 / (s.card : ℝ)) (fun a => a % p) r) = 1 := by
    rw [sum_fiberMass s (occupiedResidues A p) _ _ hmap]
    exact sum_uniform_mass s hs
  have h := inverse_card_le_collision (occupiedResidues A p) _
    (occupiedResidues_nonempty hA hp) hmass
  rw [fiberMass_sq_eq_residueMass_sq s (occupiedResidues A p) _ _ hp hmap
    (fun _ _ _ _ => Iff.rfl)] at h
  exact h

 theorem occupiedResidues_reciprocal_bound (A : Set ℕ) (s P : Finset ℕ)
    (hs : s.Nonempty) (hsA : ∀ a ∈ s, a ∈ A) (Y : ℕ) (hY : 1 ≤ Y)
    (hbound : ∀ a ∈ s, a ≤ Y) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, Real.log (p : ℝ) / ((occupiedResidues A p).card : ℝ)) ≤
      Real.log (Y : ℝ) + (1 / (s.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) := by
  have hdiam : ∀ a ∈ s, ∀ b ∈ s, Nat.dist a b ≤ Y := by
    intro a ha b hb
    rcases le_total a b with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab]
      exact (Nat.sub_le b a).trans (hbound b hb)
    · rw [Nat.dist_eq_sub_of_le_right hba]
      exact (Nat.sub_le a b).trans (hbound a ha)
  have hupper := uniformResidueCollision_upper P s hs Y hY hP hdiam
  apply le_trans _ hupper
  apply Finset.sum_le_sum
  intro p hp
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left
    (uniformResidueCollision_support_lower A s hs hsA (hP p hp).pos)
    (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))

 theorem summandPrefix_occupied_bound (A : Set ℕ) (P : Finset ℕ) (Y : ℕ)
    (hY : 1 ≤ Y) (hs : (summandPrefix A Y).Nonempty) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, Real.log (p : ℝ) / ((occupiedResidues A p).card : ℝ)) ≤
      Real.log (Y : ℝ) + (1 / ((summandPrefix A Y).card : ℝ)) *
        ∑ p ∈ P, Real.log (p : ℝ) :=
  occupiedResidues_reciprocal_bound A (summandPrefix A Y) P hs
    (fun a ha => (mem_summandPrefix A Y a).mp ha |>.1) Y hY
    (fun a ha => (mem_summandPrefix A Y a).mp ha |>.2) hP

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FullSummandResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full forbidden residue sets in the summand-size argument -/

namespace Ostmann

open scoped Classical BigOperators

 theorem mem_negativeOccupiedResidues (B : Set ℕ) (p : ℕ) (hp : 0 < p) (r : ZMod p) :
    r ∈ negativeOccupiedResidues B p ↔ ∃ b ∈ B, -(b : ZMod p) = r := by
  unfold negativeOccupiedResidues
  constructor
  · intro hr
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hr
    obtain ⟨_, b, hb, hbs⟩ := mem_occupiedResidues.mp hs
    refine ⟨b, hb, ?_⟩
    rw [← hbs, ZMod.natCast_mod] at he
    exact he
  · rintro ⟨b, hb, rfl⟩
    refine Finset.mem_image.mpr ⟨b % p, ?_, ?_⟩
    · exact mem_occupiedResidues.mpr ⟨Nat.mod_lt b hp, b, hb, rfl⟩
    · rw [ZMod.natCast_mod]

 theorem negativeOccupiedResidues_card (B : Set ℕ) (p : ℕ) :
    (negativeOccupiedResidues B p).card = (occupiedResidues B p).card := by
  unfold negativeOccupiedResidues
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  have he := (ZMod.natCast_eq_natCast_iff' a b p).mp (neg_injective hab)
  rw [Nat.mod_eq_of_lt (mem_occupiedResidues.mp ha).1,
    Nat.mod_eq_of_lt (mem_occupiedResidues.mp hb).1] at he
  exact he

 theorem allowedSummandResidues_card (B : Set ℕ) (p : ℕ) [NeZero p] :
    (allowedSummandResidues B p).card + (occupiedResidues B p).card = p := by
  rw [← negativeOccupiedResidues_card B p]
  change (Finset.univ \ negativeOccupiedResidues B p).card +
    (negativeOccupiedResidues B p).card = p
  rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, ZMod.card]

 theorem EventuallyPrimeSumset.full_residue_avoidance {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ p, p.Prime → ∀ a ∈ A, N + p < a →
      (a : ZMod p) ∉ negativeOccupiedResidues B p := by
  obtain ⟨N, hN⟩ := h.prime_not_dvd_large_sum
  refine ⟨N, ?_⟩
  intro p hp a ha hlarge hr
  obtain ⟨b, hb, he⟩ := (mem_negativeOccupiedResidues B p hp.pos _).mp hr
  apply hN p hp a ha b hb (by omega) (by omega)
  apply (ZMod.natCast_eq_zero_iff (a + b) p).mp
  rw [Nat.cast_add, ← he]
  simp

 theorem occupied_to_allowed_ratio (B : Set ℕ) (p : ℕ) [NeZero p]
    (hS : (allowedSummandResidues B p).Nonempty) :
    ((occupiedResidues B p).card : ℝ) / p ≤
      (p : ℝ) / (allowedSummandResidues B p).card - 1 := by
  have hcard := allowedSummandResidues_card B p
  have hcardR : ((allowedSummandResidues B p).card : ℝ) +
      (occupiedResidues B p).card = p := by exact_mod_cast hcard
  have hSpos : (0 : ℝ) < (allowedSummandResidues B p).card := by
    exact_mod_cast hS.card_pos
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hν : (0 : ℝ) ≤ (occupiedResidues B p).card := Nat.cast_nonneg _
  calc
    _ ≤ ((occupiedResidues B p).card : ℝ) / (allowedSummandResidues B p).card :=
      div_le_div_of_nonneg_left hν hSpos (by linarith)
    _ = _ := by
      field_simp
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact forbidden classes of finitely many distinct shifts -/

namespace Ostmann

open scoped Classical BigOperators

 theorem zmod_range_image (p : ℕ) [NeZero p] :
    ((Finset.range p).image fun r : ℕ => (r : ZMod p)) = Finset.univ := by
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    exact Finset.mem_image.mpr ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

 theorem finiteShiftAllowed_card (B : Finset ℕ) (p : ℕ) [NeZero p]
    (hB : ∀ b ∈ B, b < p) : (finiteShiftAllowed B p).card + B.card = p := by
  have hinj : Set.InjOn (fun b : ℕ => -(b : ZMod p)) B := by
    intro a ha b hb he
    have hmod := (ZMod.natCast_eq_natCast_iff' a b p).mp (neg_injective he)
    simpa only [Nat.mod_eq_of_lt (hB a ha), Nat.mod_eq_of_lt (hB b hb)] using hmod
  rw [finiteShiftAllowed, zmod_range_image, ← Finset.card_image_of_injOn hinj,
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, ZMod.card]

 theorem finiteShiftAllowed_mem_of_prime (B : Finset ℕ) (p a : ℕ) [NeZero p]
    (hp : p.Prime) (ha : p < a) (hprime : ∀ b ∈ B, (a + b).Prime) :
    (a : ZMod p) ∈ finiteShiftAllowed B p := by
  rw [finiteShiftAllowed, zmod_range_image]
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hmem
  obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hmem
  have hdvd : p ∣ a + b := by
    apply (ZMod.natCast_eq_zero_iff (a + b) p).mp
    rw [Nat.cast_add, ← he]
    simp
  have heq := ((hprime b hb).dvd_iff_eq hp.one_lt.ne').mp hdvd
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cosecant kernel in the sharp additive large sieve

The finite-kernel identity is equation (3.6) of Montgomery--Vaughan,
Hilbert's inequality, JLMS (2) 8 (1974), 73--82. The scalar majorant is
Lemma 1 there. Only these concrete trigonometric statements are used.
-/

namespace Ostmann

theorem cosecantKernel_skew (x y : ℝ) : cosecantKernel x y = -cosecantKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cosecantKernel, he]

theorem cotangentKernel_skew (x y : ℝ) : cotangentKernel x y = -cotangentKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cotangentKernel, he, div_neg]

theorem cosecantKernel_triple (x y z : ℝ)
    (hxy : Real.sin (Real.pi * (x - y)) ≠ 0)
    (hxz : Real.sin (Real.pi * (x - z)) ≠ 0)
    (hyz : Real.sin (Real.pi * (y - z)) ≠ 0) :
    cosecantKernel x y * cosecantKernel x z =
      cosecantKernel y z * (cotangentKernel x y - cotangentKernel x z) := by
  have he : Real.pi * (y - z) = Real.pi * (x - z) - Real.pi * (x - y) := by ring
  have hs := Real.sin_sub (Real.pi * (x - z)) (Real.pi * (x - y))
  rw [← he] at hs
  unfold cosecantKernel cotangentKernel
  field_simp
  nlinarith

theorem cos_quartic_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t - t + t ^ 3 / 6 := by
    dsimp [f]
    simp (disch := fun_prop)
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have ht0 : 0 ≤ t := (Set.mem_Ici.mp (interior_subset ht))
    have hs := Real.sin_ge_sub_cube ht0
    linarith
  have hh := hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) hx hx
  simpa [f] using hh

theorem sine_cosecant_majorant {x : ℝ} (hx : 0 < x) (hxp : x ≤ Real.pi / 2) :
    1 / (Real.sin x) ^ 2 + 2 * |Real.cos x / (Real.sin x) ^ 2| ≤ 3 / x ^ 2 := by
  have hx2 : x < 2 := by linarith [Real.pi_lt_four]
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxp⟩
  have hxSq : x ^ 2 ≤ 4 := by nlinarith
  have hcube := mul_le_mul_of_nonneg_right hxSq hx.le
  have hl : 0 ≤ x - x ^ 3 / 6 := by nlinarith
  have hsin := Real.sin_ge_sub_cube hx.le
  have hsq := mul_self_le_mul_self hl hsin
  have hcos := mul_le_mul_of_nonneg_left (cos_quartic_upper hx.le) (sq_nonneg x)
  have hpoly : (1 + 2 * Real.cos x) * x ^ 2 ≤ 3 * (Real.sin x) ^ 2 := by nlinarith
  rw [abs_of_nonneg (div_nonneg hc (sq_nonneg _))]
  have he : 1 / (Real.sin x) ^ 2 + 2 * (Real.cos x / (Real.sin x) ^ 2) =
      (1 + 2 * Real.cos x) / (Real.sin x) ^ 2 := by ring
  rw [he]
  exact (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos hx)).mpr hpoly

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantDistanceBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cosecant row weight depends only on distance to an integer -/

namespace Ostmann

 theorem cosecantRowWeight_eq (x y : ℝ) :
    cosecantKernel x y ^ 2 + 2 * |cosecantKernel x y * cotangentKernel x y| =
      cosecantRowWeight (x - y) := by
  unfold cosecantKernel cotangentKernel cosecantRowWeight
  congr 1
  · ring
  · congr 2
    ring

 theorem cosecantRowWeight_shift (t : ℝ) (m : ℤ) :
    cosecantRowWeight (t - m) = cosecantRowWeight t := by
  have he : Real.pi * (t - m) = Real.pi * t - (m : ℝ) * Real.pi := by ring
  have hs : |Real.sin (Real.pi * (t - m))| = |Real.sin (Real.pi * t)| := by
    rw [he, Real.sin_sub_int_mul_pi, abs_mul]
    simp
  have hc : |Real.cos (Real.pi * (t - m))| = |Real.cos (Real.pi * t)| := by
    rw [he, Real.cos_sub_int_mul_pi, abs_mul]
    simp
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  simp only [sq_abs] at hs2
  unfold cosecantRowWeight
  rw [hs2, abs_div, abs_div, hc]

 theorem cosecantRowWeight_abs (t : ℝ) : cosecantRowWeight |t| = cosecantRowWeight t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    simp [cosecantRowWeight, Real.sin_neg, Real.cos_neg]

 theorem cosecantRowWeight_bound (t d : ℝ) (m : ℤ)
    (hd : 0 < d) (hdhalf : d ≤ 1 / 2) (he : |t - m| = d) :
    cosecantRowWeight t ≤ 3 / (Real.pi ^ 2 * d ^ 2) := by
  rw [← cosecantRowWeight_shift t m, ← cosecantRowWeight_abs, he]
  have hp : 0 < Real.pi * d := mul_pos Real.pi_pos hd
  have hh : Real.pi * d ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hb := sine_cosecant_majorant hp hh
  simpa only [cosecantRowWeight, mul_pow] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SeparatedInverseSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-sided inverse-square estimate for separated sample points -/

namespace Ostmann

open scoped BigOperators

 theorem ordered_separated_lower {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    ∀ i, δ * (i.val + 1) ≤ x i := by
  have hi : ∀ k : ℕ, ∀ hk : k < n, δ * ((k : ℝ) + 1) ≤ x ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; simpa using hfirst ⟨0, hk⟩
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hg := hgap ⟨k, by omega⟩ ⟨k + 1, hk⟩ (by simp)
      push_cast
      linarith
  intro i
  exact hi i.val i.isLt

 theorem finite_positive_inverse_squares (n : ℕ) :
    (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) ≤ Real.pi ^ 2 / 6 := by
  have he : (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) =
      ∑ j ∈ Finset.range (n + 1), 1 / (j : ℝ) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) n,
      Finset.sum_range_succ']
    simp
  rw [he, ← hasSum_zeta_two.tsum_eq]
  exact hasSum_zeta_two.summable.sum_le_tsum _ (fun j _ => by positivity)

 theorem ordered_separated_inverse_squares {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    (∑ i, 1 / (x i) ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  have hx := ordered_separated_lower x δ hfirst hgap
  have hb (i : Fin n) : 1 / (x i) ^ 2 ≤
      (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := by
    have hi : 0 < (i.val : ℝ) + 1 := by positivity
    have hxi : 0 < x i := lt_of_lt_of_le hδ (hfirst i)
    have hs : (δ * ((i.val : ℝ) + 1)) ^ 2 ≤ (x i) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hx i) 2
    calc
      _ ≤ 1 / (δ * ((i.val : ℝ) + 1)) ^ 2 := one_div_le_one_div_of_le (by positivity) hs
      _ = _ := by simp only [mul_pow, one_div, mul_inv]
  calc
    _ ≤ ∑ i : Fin n, (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := Finset.sum_le_sum (fun i _ => hb i)
    _ = (δ ^ 2)⁻¹ * ∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (δ ^ 2)⁻¹ * (Real.pi ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left (finite_positive_inverse_squares n) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SeparatedSetSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse-square row sum for a finite separated set -/

namespace Ostmann

open scoped BigOperators

 theorem positive_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  classical
  let e := S.orderEmbOfFin rfl
  have he (i : Fin S.card) : e i ∈ S := S.orderEmbOfFin_mem rfl i
  have hg (i j : Fin S.card) (hij : i < j) : δ ≤ e j - e i := by
    have hij' : e i < e j := e.strictMono hij
    have hh := hsep (e j) (he j) (e i) (he i) (ne_of_gt hij')
    rwa [abs_of_pos (sub_pos.mpr hij')] at hh
  have hh := ordered_separated_inverse_squares (fun i => e i) δ hδ
    (fun i => hfirst _ (he i)) hg
  have hs : (∑ x ∈ S, 1 / x ^ 2) = ∑ i : Fin S.card, 1 / (e i) ^ 2 := by
    conv_lhs => rw [← S.image_orderEmbOfFin_univ rfl]
    rw [Finset.sum_image]
    exact fun i _ j _ hij => e.injective hij
  rwa [hs]

 theorem separated_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ |x|)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let P := S.filter (fun x => 0 < x)
  let N := S.filter (fun x => ¬0 < x)
  let R := N.image (fun x => -x)
  have hP := positive_set_inverse_squares P δ hδ
    (fun x hx => by
      have h := Finset.mem_filter.mp hx
      simpa only [abs_of_pos h.2] using hfirst x h.1)
    (fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
  have hRfirst (x : ℝ) (hx : x ∈ R) : δ ≤ x := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_filter.mp hy
    simpa only [abs_of_nonpos (le_of_not_gt hy'.2)] using hfirst y hy'.1
  have hRsep (x : ℝ) (hx : x ∈ R) (y : ℝ) (hy : y ∈ R) (hxy : x ≠ y) : δ ≤ |x - y| := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hh := hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (fun hab => hxy (congrArg Neg.neg hab))
    simpa only [neg_sub_neg, abs_sub_comm] using hh
  have hR := positive_set_inverse_squares R δ hδ hRfirst hRsep
  have hsum : (∑ x ∈ P, 1 / x ^ 2) + (∑ x ∈ N, 1 / x ^ 2) = ∑ x ∈ S, 1 / x ^ 2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have he : (∑ x ∈ R, 1 / x ^ 2) = ∑ x ∈ N, 1 / x ^ 2 := by
    rw [Finset.sum_image]
    · simp
    · exact fun _ _ _ _ hab => neg_injective hab
  rw [he] at hR
  rw [← hsum]
  have hid : Real.pi ^ 2 / (3 * δ ^ 2) = 2 * (Real.pi ^ 2 / (6 * δ ^ 2)) := by ring
  rw [hid]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CircleSeparatedPoints
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering a separated finite family on the circle -/

namespace Ostmann

open scoped BigOperators

 theorem centeredCircleRemainder_bounds (t : ℝ) :
    -(1 / 2) ≤ centeredCircleRemainder t ∧ centeredCircleRemainder t < 1 / 2 := by
  have hl := Int.floor_le (t + 1 / 2)
  have hu := Int.lt_floor_add_one (t + 1 / 2)
  dsimp [centeredCircleRemainder]
  constructor <;> linarith

 theorem circleSeparated_sine_ne_zero {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hx : CircleSeparated x δ) {s t : ι} (hst : s ≠ t) :
    Real.sin (Real.pi * (x s - x t)) ≠ 0 := by
  intro hz
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hz
  have he : x s - x t - (m : ℝ) = 0 := by nlinarith [Real.pi_pos]
  have hh := hx s t hst m
  rw [he, abs_zero] at hh
  linarith

 theorem circleSeparated_remainders {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hx : CircleSeparated x δ) (center s t : ι) (hst : s ≠ t) :
    δ ≤ |centeredCircleRemainder (x s - x center) -
      centeredCircleRemainder (x t - x center)| := by
  have hh := hx s t hst (⌊x s - x center + 1 / 2⌋ - ⌊x t - x center + 1 / 2⌋)
  push_cast at hh
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; dsimp [centeredCircleRemainder]; ring)

 theorem circleSeparated_inverse_square_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s ∈ Finset.univ.erase center,
      1 / centeredCircleRemainder (x s - x center) ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  let S := F.image r
  have hfirst (s : ι) (hs : s ∈ F) : δ ≤ |r s| :=
    hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
  have hinj : Set.InjOn r F := by
    intro s hs t ht he
    by_contra hst
    have hb := circleSeparated_remainders x δ hx center s t hst
    change δ ≤ |r s - r t| at hb
    rw [he, sub_self, abs_zero] at hb
    linarith
  have hb := separated_set_inverse_squares S δ hδ (by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    exact hfirst s hs) (by
    intro y hy z hz hyz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact circleSeparated_remainders x δ hx center s t (fun hst => hyz (congrArg r hst)))
  have he : (∑ y ∈ S, 1 / y ^ 2) = ∑ s ∈ F, 1 / (r s) ^ 2 := by
    exact Finset.sum_image hinj
  rwa [he] at hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_ReducedFractionSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact circle separation of reduced fractions -/

namespace Ostmann

 theorem reduced_fraction_cross_injective (q r h k : ℕ) (hq : 0 < q)
    (_hr : 0 < r) (hc : h.Coprime q) (kc : k.Coprime r) (he : h * r = k * q) :
    q = r ∧ h = k := by
  have hqr : q ∣ r := hc.symm.dvd_mul_left.mp (by rw [he]; exact dvd_mul_left q k)
  have hrq : r ∣ q := kc.symm.dvd_mul_left.mp (by rw [← he]; exact dvd_mul_left r h)
  have hqeq : q = r := Nat.dvd_antisymm hqr hrq
  refine ⟨hqeq, ?_⟩
  subst r
  exact Nat.eq_of_mul_eq_mul_right hq (by simpa only [mul_comm] using he)

 theorem reduced_fraction_circle_separation (Q q r h k : ℕ)
    (hq : 0 < q) (hr : 0 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hh : h < q) (hk : k < r) (hc : h.Coprime q) (kc : k.Coprime r)
    (hne : (q, h) ≠ (r, k)) (m : ℤ) :
    1 / (Q : ℝ) ^ 2 ≤ |(h : ℝ) / q - (k : ℝ) / r - m| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hQR : (0 : ℝ) < Q := lt_of_lt_of_le hqR (by exact_mod_cast hqQ)
  let t : ℝ := (h : ℝ) / q - (k : ℝ) / r - m
  have ht : t ≠ 0 := by
    intro ht0
    have hhlo : 0 ≤ (h : ℝ) / q := by positivity
    have hklo : 0 ≤ (k : ℝ) / r := by positivity
    have hhhi : (h : ℝ) / q < 1 := (div_lt_one hqR).mpr (by exact_mod_cast hh)
    have hkhi : (k : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast hk)
    have hmlo : (-1 : ℝ) < m := by dsimp [t] at ht0; linarith
    have hmhi : (m : ℝ) < 1 := by dsimp [t] at ht0; linarith
    have hm : m = 0 := by
      have hlo : (-1 : ℤ) < m := by exact_mod_cast hmlo
      have hhi : m < (1 : ℤ) := by exact_mod_cast hmhi
      omega
    have heR : (h : ℝ) * r = (k : ℝ) * q := by
      dsimp [t] at ht0
      rw [hm, Int.cast_zero, sub_zero, sub_eq_zero] at ht0
      exact (div_eq_div_iff hqR.ne' hrR.ne').mp ht0
    have heN : h * r = k * q := by exact_mod_cast heR
    obtain ⟨hqr, hhk⟩ := reduced_fraction_cross_injective q r h k hq hr hc kc heN
    exact hne (Prod.ext hqr hhk)
  let N : ℤ := (h : ℤ) * r - (k : ℤ) * q - m * q * r
  have hN : (N : ℝ) = (q : ℝ) * r * t := by
    dsimp [N, t]
    push_cast
    field_simp
  have hN0 : N ≠ 0 := by
    intro hzero
    rw [hzero, Int.cast_zero] at hN
    exact ht ((mul_eq_zero.mp hN.symm).resolve_left (mul_ne_zero hqR.ne' hrR.ne'))
  have hN1 : (1 : ℤ) ≤ |N| := Int.one_le_abs hN0
  have hN1R : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast hN1
  rw [hN, abs_mul, abs_mul, abs_of_pos hqR, abs_of_pos hrR] at hN1R
  have hprod : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by
    have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hrQ' : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
    nlinarith
  have hhprod := mul_le_mul_of_nonneg_right hprod (abs_nonneg t)
  change 1 / (Q : ℝ) ^ 2 ≤ |t|
  apply (div_le_iff₀ (sq_pos_of_pos hQR)).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_HermitianEigenvector
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Hermitian eigenvector cancellation -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem hermitian_eigenvector_left {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) (v : ι → ℂ) :
    star u ⬝ᵥ (A *ᵥ v) = (μ : ℂ) * (star u ⬝ᵥ v) := by
  have h : star u ⬝ᵥ (A *ᵥ v) = star (A *ᵥ u) ⬝ᵥ v := by
    rw [Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]
  rw [h, heig, star_smul, smul_dotProduct]
  simp

theorem hermitian_eigenvector_commutator {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (D : Matrix ι ι ℂ) (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) :
    star u ⬝ᵥ ((D * A - A * D) *ᵥ u) = 0 := by
  rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec,
    heig, mulVec_smul, dotProduct_smul, hermitian_eigenvector_left hA u μ heig]
  simp only [smul_eq_mul, sub_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantMatrix
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact square of the finite cosecant matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
 theorem imaginaryKernelMatrix_hermitian (h : ι → ι → ℝ)
    (hskew : ∀ s t, h s t = -h t s) : (imaginaryKernelMatrix h).IsHermitian := by
  ext s t
  simp only [imaginaryKernelMatrix, conjTranspose_apply, Matrix.of_apply, map_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal]
  rw [hskew t s]
  push_cast
  ring

 theorem imaginaryKernelMatrix_square_entry (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (imaginaryKernelMatrix h * imaginaryKernelMatrix h) s t =
      (if s = t then ((∑ r, h r s ^ 2 : ℝ) : ℂ) else 0) +
        (h s t : ℂ) * ((∑ r, k r s : ℝ) - ∑ r, k r t) +
          2 * (h s t : ℂ) * (k s t : ℂ) := by
  have he (r : ι) : imaginaryKernelMatrix h s r * imaginaryKernelMatrix h r t =
      ((h r s * h r t : ℝ) : ℂ) := by
    dsimp [imaginaryKernelMatrix]
    rw [hskew s r]
    push_cast
    calc
      _ = -(Complex.I * Complex.I) * ((h r s : ℂ) * (h r t : ℂ)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [← Complex.ofReal_sum, skew_kernel_square_entry h k hdiag kdiag kskew htriple]
  push_cast
  by_cases hst : s = t <;> simp [hst]

 theorem imaginaryKernelMatrix_square (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) :
    let A : Matrix ι ι ℂ := imaginaryKernelMatrix h
    let D : Matrix ι ι ℂ := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
    A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
      (Complex.I • (D * A - A * D) : Matrix ι ι ℂ) +
        (2 : ℂ) • Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ)) := by
  dsimp only
  ext s t
  rw [imaginaryKernelMatrix_square_entry h k hdiag kdiag hskew kskew htriple]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    imaginaryKernelMatrix, Matrix.of_apply]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_mul,
    ]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SymmetricQuadraticBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite quadratic bound for the cosecant row estimate -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem real_symmetric_quadratic_upper (v : ι → ι → ℝ)
    (hv : ∀ s t, v s t = v t s) (u : ι → ℂ) :
    ‖star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u)‖ ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
  have he : star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u) =
      ∑ s, ∑ t, star (u s) * (v s t : ℂ) * u t := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  have hswap : (∑ s, ∑ t, |v s t| * ‖u t‖ ^ 2) =
      ∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [hv t s]
  have hfactor : (∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul, mul_comm]
  have havg : (∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    simp_rw [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hswap]
    rw [hfactor]
    ring
  rw [he]
  calc
    _ ≤ ∑ s, ‖∑ t, star (u s) * (v s t : ℂ) * u t‖ := norm_sum_le _ _
    _ ≤ ∑ s, ∑ t, ‖star (u s) * (v s t : ℂ) * u t‖ :=
      Finset.sum_le_sum (fun s _ => norm_sum_le _ _)
    _ = ∑ s, ∑ t, |v s t| * ‖u s‖ * ‖u t‖ := by
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      have hh := mul_le_mul_of_nonneg_left (sq_nonneg (‖u s‖ - ‖u t‖)) (abs_nonneg (v s t))
      nlinarith
    _ = _ := havg

end Ostmann

end OAI
end

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

theorem complex_diagonal_quadratic (d : ι → ℝ) (u : ι → ℂ) :
    star u ⬝ᵥ ((Matrix.diagonal (fun s => (d s : ℂ))) *ᵥ u) =
      ((∑ s, d s * ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  rw [show star (u s) * ((d s : ℂ) * u s) = (d s : ℂ) * (star (u s) * u s) by ring,
    Complex.star_def, Complex.conj_mul']

omit [DecidableEq ι] in
 theorem complex_self_quadratic (u : ι → ℂ) :
    star u ⬝ᵥ u = ((∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [Complex.star_def] using Complex.conj_mul' (u s)

 theorem kernel_eigenvalue_bound (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t))
    (B μ : ℝ) (hrow : ∀ s, (∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r| ≤ B)
    (u : ι → ℂ) (hu : 0 < ∑ s, ‖u s‖ ^ 2)
    (heig : imaginaryKernelMatrix h *ᵥ u = (μ : ℂ) • u) : μ ^ 2 ≤ B := by
  let A := imaginaryKernelMatrix h
  let D := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
  let V : Matrix ι ι ℂ := Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ))
  have hA : A.IsHermitian := imaginaryKernelMatrix_hermitian h hskew
  have hcomm := hermitian_eigenvector_commutator hA D u μ heig
  have hsq : star u ⬝ᵥ ((A * A) *ᵥ u) =
      ((μ ^ 2 * ∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mulVec_mulVec, heig, mulVec_smul, heig, smul_smul, dotProduct_smul,
      complex_self_quadratic]
    push_cast
    simp only [smul_eq_mul, pow_two]
  have hidentity := imaginaryKernelMatrix_square h k hdiag kdiag hskew kskew htriple
  change A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
    Complex.I • (D * A - A * D) + (2 : ℂ) • V at hidentity
  rw [hidentity, add_mulVec, sub_mulVec, smul_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, hcomm, smul_zero, sub_zero, smul_mulVec, dotProduct_smul,
    complex_diagonal_quadratic] at hsq
  have hreal := congrArg Complex.re hsq
  have htwo (z : ℂ) : ((2 : ℂ) • z).re = 2 * z.re := by simp [smul_eq_mul, Complex.mul_re]
  simp only [Complex.add_re, Complex.ofReal_re, htwo] at hreal
  have hsym : ∀ s t, h s t * k s t = h t s * k t s := by
    intro s t
    rw [hskew s t, kskew s t]
    ring
  have hv := real_symmetric_quadratic_upper (fun s t => h s t * k s t) hsym u
  have hvr : (star u ⬝ᵥ (V *ᵥ u)).re ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |h s t * k s t| :=
    (Complex.re_le_norm _).trans hv
  have hsum : (∑ s, (∑ r, h r s ^ 2) * ‖u s‖ ^ 2) +
      2 * (∑ s, ‖u s‖ ^ 2 * ∑ r, |h s r * k s r|) ≤
        B * ∑ s, ‖u s‖ ^ 2 := by
    calc
      _ = ∑ s, ‖u s‖ ^ 2 * ((∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r|) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro s _
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ ∑ s, ‖u s‖ ^ 2 * B := Finset.sum_le_sum (fun s _ =>
        mul_le_mul_of_nonneg_left (hrow s) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hfinal : μ ^ 2 * (∑ s, ‖u s‖ ^ 2) ≤ B * (∑ s, ‖u s‖ ^ 2) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hu).mp hfinal

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
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantRowSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp row budget for the cosecant matrix -/

namespace Ostmann

open scoped BigOperators

 theorem cosecant_row_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s, cosecantKernel (x s) (x center) ^ 2) +
        2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| ≤
      1 / δ ^ 2 := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  have he (s : ι) : cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s) =
      cosecantKernel (x s) (x center) * cotangentKernel (x s) (x center) := by
    rw [cosecantKernel_skew (x center) (x s), cotangentKernel_skew (x center) (x s)]
    ring
  have hsum : (∑ s, cosecantKernel (x s) (x center) ^ 2) +
      2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| =
        ∑ s ∈ F, cosecantRowWeight (x s - x center) := by
    simp_rw [he]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    simp_rw [cosecantRowWeight_eq]
    apply (Finset.sum_erase_add _ _ (Finset.mem_univ center)).symm.trans ?_
    simp [cosecantRowWeight, F]
  have hb (s : ι) (hs : s ∈ F) :
      cosecantRowWeight (x s - x center) ≤ 3 / (Real.pi ^ 2 * (r s) ^ 2) := by
    have hd := hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
    change δ ≤ |r s| at hd
    have hhalf : |r s| ≤ 1 / 2 := abs_le.mpr
      ⟨(centeredCircleRemainder_bounds _).1, (centeredCircleRemainder_bounds _).2.le⟩
    have hh := cosecantRowWeight_bound (x s - x center) |r s|
      ⌊x s - x center + 1 / 2⌋ (lt_of_lt_of_le hδ hd) hhalf rfl
    simpa only [sq_abs] using hh
  rw [hsum]
  calc
    _ ≤ ∑ s ∈ F, 3 / (Real.pi ^ 2 * (r s) ^ 2) := Finset.sum_le_sum hb
    _ = (3 / Real.pi ^ 2) * ∑ s ∈ F, 1 / (r s) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ (3 / Real.pi ^ 2) * (Real.pi ^ 2 / (3 * δ ^ 2)) :=
      mul_le_mul_of_nonneg_left (circleSeparated_inverse_square_row x δ hδ hx center) (by positivity)
    _ = _ := by field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_HermitianNormBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing a finite Hermitian eigenvalue bound to its quadratic form -/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem hermitian_norm_bound {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (B : ℝ) (hB : 0 ≤ B) (heig : ∀ i, |hA.eigenvalues i| ≤ B) : ‖A‖ ≤ B := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  simpa only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.norm_real,
    Real.norm_eq_abs] using heig i

 theorem matrix_quadratic_norm_bound (A : Matrix ι ι ℂ) (B : ℝ)
    (hB : ‖A‖ ≤ B) (u : ι → ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ u)‖ ≤ B * ∑ i, ‖u i‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let w : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm (A *ᵥ u)
  have hinner : inner ℂ v w = star u ⬝ᵥ (A *ᵥ u) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hv : ‖v‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := EuclideanSpace.norm_sq_eq v
  have hw : ‖w‖ ≤ B * ‖v‖ := (Matrix.l2_opNorm_mulVec A v).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  rw [← hinner]
  calc
    _ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (B * ‖v‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg v)
    _ = B * ∑ i, ‖u i‖ ^ 2 := by rw [← hv]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantHilbertBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Montgomery--Vaughan's finite unweighted Hilbert inequality

This is Theorem 1, inequality (1.2), of Montgomery--Vaughan (1974).
It is derived from the checked finite kernel cancellation and row estimate.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
 theorem cosecantMatrix_hermitian (x : ι → ℝ) : (cosecantMatrix x).IsHermitian :=
  imaginaryKernelMatrix_hermitian _ (fun _ _ => cosecantKernel_skew _ _)

 theorem cosecant_eigenvalue_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (μ : ℝ) (u : ι → ℂ)
    (hu : 0 < ∑ s, ‖u s‖ ^ 2) (heig : cosecantMatrix x *ᵥ u = (μ : ℂ) • u) :
    μ ^ 2 ≤ 1 / δ ^ 2 := by
  exact kernel_eigenvalue_bound
    (fun s t => cosecantKernel (x s) (x t))
    (fun s t => cotangentKernel (x s) (x t))
    (fun _ => cosecantKernel_self _) (fun _ => cotangentKernel_self _)
    (fun _ _ => cosecantKernel_skew _ _) (fun _ _ => cotangentKernel_skew _ _)
    (fun r s t hrs hrt hst => cosecantKernel_triple _ _ _
      (circleSeparated_sine_ne_zero x δ hδ hx hrs)
      (circleSeparated_sine_ne_zero x δ hδ hx hrt)
      (circleSeparated_sine_ne_zero x δ hδ hx hst))
    (1 / δ ^ 2) μ (cosecant_row_sum_bound x δ hδ hx) u hu heig

 theorem cosecantMatrix_norm_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) : ‖cosecantMatrix x‖ ≤ 1 / δ := by
  apply hermitian_norm_bound (cosecantMatrix_hermitian x) (1 / δ) (by positivity)
  intro i
  let hA := cosecantMatrix_hermitian x
  have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hu : 0 < ∑ s, ‖(hA.eigenvectorBasis i) s‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, hnorm]
    norm_num
  have hb := cosecant_eigenvalue_bound x δ hδ hx (hA.eigenvalues i)
    (hA.eigenvectorBasis i) hu (hA.mulVec_eigenvectorBasis i)
  have hinv : 0 < 1 / δ := by positivity
  have heq : 1 / δ ^ 2 = (1 / δ) ^ 2 := by ring
  rw [heq] at hb
  nlinarith [sq_abs (hA.eigenvalues i), abs_nonneg (hA.eigenvalues i)]

 theorem cosecant_hilbert_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (u : ι → ℂ) :
    ‖∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t‖ ≤
      (1 / δ) * ∑ s, ‖u s‖ ^ 2 := by
  have hb := matrix_quadratic_norm_bound (cosecantMatrix x) (1 / δ)
    (cosecantMatrix_norm_bound x δ hδ hx) u
  have he : star u ⬝ᵥ (cosecantMatrix x *ᵥ u) =
      Complex.I * (∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t) := by
    simp only [dotProduct, mulVec, Pi.star_apply, cosecantMatrix, imaginaryKernelMatrix,
      Matrix.of_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he, norm_mul, Complex.norm_I, one_mul] at hb
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SieveGeometricKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite exponential kernel for the additive large sieve -/

namespace Ostmann

open scoped BigOperators

 theorem sieveHalfPhase_add (s t : ℝ) :
    sieveHalfPhase (s + t) = sieveHalfPhase s * sieveHalfPhase t := by
  simp only [sieveHalfPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

 theorem sieveHalfPhase_sine (t : ℝ) :
    (2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ) =
      sieveHalfPhase t - sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

 theorem sieveHalfPhase_two_step (s t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) * sieveHalfPhase s =
      sieveHalfPhase (s + t) - sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_sine, sieveHalfPhase_add, sub_eq_add_neg s t, sieveHalfPhase_add]
  ring

 theorem sieve_geometric_kernel_mul (M : ℕ) (J t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) *
      (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
        sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hs := sieveHalfPhase_two_step (2 * (J + M) * t) t
    rw [show 2 * (J + (M : ℝ)) * t + t = (2 * (J + (M + 1 : ℕ)) - 1) * t by
      push_cast; ring,
      show 2 * (J + (M : ℝ)) * t - t = (2 * (J + M) - 1) * t by ring] at hs
    rw [hs]
    ring

 theorem sieve_geometric_kernel (M : ℕ) (J t : ℝ)
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
      ((sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) /
        ((2 : ℂ) * Complex.I)) * (Real.sin (Real.pi * t) : ℂ)⁻¹ := by
  have hs := sieve_geometric_kernel_mul M J t
  have htC : (Real.sin (Real.pi * t) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hfactor : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero hfactor htC))
  rw [hs, div_eq_mul_inv]
  symm
  calc
    _ = (((2 : ℂ) * Complex.I) * ((2 : ℂ) * Complex.I)⁻¹) *
        ((Real.sin (Real.pi * t) : ℂ) * (Real.sin (Real.pi * t) : ℂ)⁻¹) *
          (sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hfactor, mul_inv_cancel₀ htC]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SievePhaseGram
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite Gram expansion of the large-sieve phase matrix -/

namespace Ostmann

open scoped BigOperators

 theorem sieveHalfPhase_star (t : ℝ) : star (sieveHalfPhase t) = sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

 theorem sieveHalfPhase_difference (s t : ℝ) :
    sieveHalfPhase s * star (sieveHalfPhase t) = sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_star, ← sieveHalfPhase_add, sub_eq_add_neg]

 theorem finite_complex_norm_expansion {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ((‖∑ s, f s‖ ^ 2 : ℝ) : ℂ) = ∑ s, ∑ t, f s * star (f t) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [← Complex.star_def, star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

 theorem sieve_phase_gram {ι : Type*} [Fintype ι] (x : ι → ℝ) (b : ι → ℂ)
    (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ∑ s, ∑ t, b s * star (b t) *
        ∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t)) := by
  simp only [Complex.ofReal_sum, finite_complex_norm_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [star_mul]
  rw [show 2 * (J + (n : ℝ)) * (x s - x t) =
    2 * (J + (n : ℝ)) * x s - 2 * (J + (n : ℝ)) * x t by ring,
    ← sieveHalfPhase_difference]
  ring

 theorem twisted_cosecant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (b : ι → ℂ) (L : ℝ) :
    ‖∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)‖ ≤ (1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  let u := fun s => star (b s * sieveHalfPhase (L * x s))
  have he : (∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)) =
      ∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    simp only [u, star_star, star_mul]
    rw [show L * (x s - x t) = L * x s - L * x t by ring,
      ← sieveHalfPhase_difference]
    ring
  rw [he]
  have hb := cosecant_hilbert_bound x δ hδ hx u
  simpa only [u, norm_star, norm_mul, sieveHalfPhase_norm, mul_one] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SieveDualEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp dual large-sieve estimate from the finite Hilbert inequality -/

namespace Ostmann

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
 theorem sieve_pair_kernel (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (s t : ι) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t))) =
      (if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ) := by
  by_cases hst : s = t
  · subst t
    simp
  · rw [ite_eq_right hst, zero_add]
    simpa only [cosecantKernel, Complex.ofReal_inv] using
      sieve_geometric_kernel M J (x s - x t) (circleSeparated_sine_ne_zero x δ hδ hx hst)

 theorem sieve_dual_energy_identity (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)) := by
  rw [sieve_phase_gram]
  simp_rw [sieve_pair_kernel x δ hδ hx M J]
  have he (s t : ι) : b s * star (b t) *
      ((if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ)) =
      (if s = t then (M : ℂ) * ((‖b s‖ ^ 2 : ℝ) : ℂ) else 0) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (b s * star (b t) * sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ) -
            b s * star (b t) * sieveHalfPhase ((2 * J - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ)) := by
    by_cases hst : s = t
    · subst t
      simp only [↓reduceIte, sub_self, mul_zero, sieveHalfPhase_zero,
        cosecantKernel_self, Complex.ofReal_zero, mul_one, add_zero]
      rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
      ring
    · simp only [hst, ↓reduceIte, zero_add, div_eq_mul_inv]
      ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum,
    Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_mul, twistedCosecantSum]

 theorem sieve_dual_energy_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    (∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  have hi := sieve_dual_energy_identity x δ hδ hx b M J
  have htop := twisted_cosecant_bound x δ hδ hx b (2 * (J + M) - 1)
  have hbottom := twisted_cosecant_bound x δ hδ hx b (2 * J - 1)
  change ‖twistedCosecantSum x b (2 * (J + M) - 1)‖ ≤ _ at htop
  change ‖twistedCosecantSum x b (2 * J - 1)‖ ≤ _ at hbottom
  have htri := norm_add_le (((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) : ℂ)
    (((2 : ℂ) * Complex.I)⁻¹ *
      (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)))
  have hdiff := norm_sub_le (twistedCosecantSum x b (2 * (J + M) - 1))
    (twistedCosecantSum x b (2 * J - 1))
  rw [← hi] at htri
  have hE : 0 ≤ ∑ s, ‖b s‖ ^ 2 := Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hN : 0 ≤ ∑ n ∈ Finset.range M,
      ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg M) hE),
    norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_I] at htri
  norm_num at htri
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SeparatedAdditiveSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite additive sieve for circle-separated frequencies -/

namespace Ostmann

open Matrix
open scoped BigOperators

 theorem sievePhaseMatrix_adjoint {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (M : ℕ) (J : ℝ) (b : ι → ℂ) (n : Fin M) :
    ((sievePhaseMatrix x M J)ᴴ *ᵥ b) n =
      star (∑ s, star (b s) * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)) := by
  simp only [mulVec, dotProduct, conjTranspose_apply, sievePhaseMatrix, Matrix.of_apply,
    star_sum, star_mul, star_star]

 theorem separated_additive_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (c : Fin M → ℂ) :
    (∑ s, ‖∑ n, c n * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ n, ‖c n‖ ^ 2 := by
  have hdual (b : ι → ℂ) :
      (∑ n, ‖((sievePhaseMatrix x M J)ᴴ *ᵥ b) n‖ ^ 2) ≤
        ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
    simp only [sievePhaseMatrix_adjoint, norm_star]
    have hb := sieve_dual_energy_bound x δ hδ hx (fun s => star (b s)) M J
    rw [← Fin.sum_univ_eq_sum_range] at hb
    simpa only [norm_star] using hb
  have hK : 0 ≤ (M : ℝ) + 1 / δ := by positivity
  have h := finite_matrix_duality (sievePhaseMatrix x M J) ((M : ℝ) + 1 / δ) hK hdual c
  simpa only [mulVec, dotProduct, sievePhaseMatrix, Matrix.of_apply, mul_comm] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_AdditiveSieveProof
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published additive large sieve, with its precise downstream constant

The finite cosecant Hilbert inequality and duality prove the separated-frequency
estimate. Reduced fractions of denominator at most Q are 1/Q²-separated.
This proves the specialization of Montgomery--Vaughan (1973), Theorem 1,
used throughout the conditional development.
-/

namespace Ostmann

open scoped BigOperators

 theorem reducedFractionPoint_separated (Q : ℕ) :
    CircleSeparated (reducedFractionPoint Q) (1 / (Q : ℝ) ^ 2) := by
  intro s t hst m
  rcases s with ⟨⟨q, hq⟩, ⟨h, hh⟩⟩
  rcases t with ⟨⟨r, hr⟩, ⟨k, hk⟩⟩
  simp only [Finset.mem_Icc] at hq hr
  simp only [reducedNumerators, Finset.mem_filter, Finset.mem_range] at hh hk
  have hne : (q, h) ≠ (r, k) := by
    intro he
    have hqr := congrArg Prod.fst he
    have hhk := congrArg Prod.snd he
    dsimp at hqr hhk
    subst r
    subst k
    exact hst rfl
  exact reduced_fraction_circle_separation Q q r h k (by omega) (by omega)
    hq.2 hr.2 hh.1 hk.1 hh.2 hk.2 hne m

 theorem sieveAdditivePhase_eq_half (q h : ℕ) (J : ℤ) (n : ℕ) :
    sieveAdditivePhase q h (J + (n : ℤ)) =
      sieveHalfPhase (2 * ((J : ℝ) + (n : ℝ)) * ((h : ℝ) / q)) := by
  unfold sieveAdditivePhase sieveHalfPhase
  congr 1
  push_cast
  ring

 theorem reducedFraction_sum (Q : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ s : ReducedFractionIndex Q, f s.1.val s.2.val) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q, f q h := by
  rw [Fintype.sum_sigma]
  change (∑ q : Finset.Icc 1 Q, ∑ h : reducedNumerators q.val, f q.val h.val) = _
  simp_rw [Finset.sum_coe_sort]
  exact Finset.sum_coe_sort (Finset.Icc 1 Q)
    (fun q : ℕ => ∑ h ∈ reducedNumerators q, f q h)

 theorem publishedAdditiveLargeSieve : PublishedAdditiveLargeSieve := by
  classical
  intro M Q _hM hQ J c
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hδ : 0 < 1 / (Q : ℝ) ^ 2 := by positivity
  have h := separated_additive_sieve (reducedFractionPoint Q) (1 / (Q : ℝ) ^ 2)
    hδ (reducedFractionPoint_separated Q) M (J : ℝ) c
  have hconst : 1 / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by field_simp
  rw [hconst] at h
  change (∑ s : ReducedFractionIndex Q,
    ‖∑ n, c n * sieveHalfPhase (2 * ((J : ℝ) + (n.val : ℝ)) *
      ((s.2.val : ℝ) / s.1.val))‖ ^ 2) ≤ _ at h
  rw [reducedFraction_sum Q (fun q h =>
    ‖∑ n, c n * sieveHalfPhase (2 * ((J : ℝ) + (n.val : ℝ)) *
      ((h : ℝ) / q))‖ ^ 2)] at h
  simpa only [additiveSieveSum, sieveAdditivePhase_eq_half] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSubsetMainTerm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive empty-coordinate term in the subset large sieve -/

namespace Ostmann

open scoped Classical BigOperators

 theorem prime_subset_main_term (ls : PublishedAdditiveLargeSieve)
    {n M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (G : Finset (Finset (Fin n))) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (hprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q)
    (ha : ∀ R ∈ G, ∀ x ∈ A, ∀ i ∈ R, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i) :
    (∑ R ∈ G, ∏ i ∈ R, ((p i : ℝ) / (S i).card - 1)) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  apply le_trans _ (prime_subset_sieve_bound ls p hc S G hQ hM A hA J hprod ha)
  apply Finset.sum_le_sum
  intro R hR
  have hnonneg (T : Finset (Fin n)) (_hT : T ∈ R.powerset) :
      0 ≤ subsetSieveCoefficient p S R T *
        centeredSubsetEnergy p S T A (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i))) :=
    mul_nonneg (subsetSieveCoefficient_nonneg p S R T (fun i _ => hS i))
      (centeredSubsetEnergy_nonneg p S T A _)
  have h := Finset.single_le_sum hnonneg (show ∅ ∈ R.powerset by simp)
  rw [centeredSubsetEnergy_empty p S A hA, mul_one] at h
  simpa only [subsetSieveCoefficient, Finset.prod_empty, one_mul, Finset.sdiff_empty] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSetSupportSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The support sieve indexed by actual finite sets of primes -/

namespace Ostmann

open scoped Classical BigOperators

 theorem prime_set_support_sieve {M Q : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (S : ∀ p : ℕ, Finset (ZMod p))
    (hS : ∀ p ∈ P, (S p).Nonempty) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (ha : ∀ x ∈ A, ∀ p ∈ P, ((J + (x.val : ℤ) : ℤ) : ZMod p) ∈ S p) :
    (∑ U ∈ boundedSieveSubsets P Q, ∏ p ∈ U, ((p : ℝ) / (S p).card - 1)) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  let e : Fin P.card ≃ P := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin P).symm
  let p : Fin P.card → ℕ := fun i => (e i).val
  have hinj : Function.Injective p := fun i j hij => e.injective (Subtype.ext hij)
  have hmem (i : Fin P.card) : p i ∈ P := (e i).property
  have hcover : ∀ q ∈ P, ∃ i : Fin P.card, p i = q := by
    intro q hq
    refine ⟨e.symm ⟨q, hq⟩, ?_⟩
    simp only [p, Equiv.apply_symm_apply]
  let : ∀ i, Fact (p i).Prime := fun i => ⟨hP _ (hmem i)⟩
  have hc : Pairwise (fun i j => (p i).Coprime (p j)) := by
    intro i j hij
    exact (Nat.coprime_primes (hP _ (hmem i)) (hP _ (hmem j))).mpr
      (fun he => hij (hinj he))
  let G := (Finset.univ : Finset (Fin P.card)).powerset.filter
    (fun R => (∏ i ∈ R, p i) ≤ Q)
  have hGprod : ∀ R ∈ G, (∏ i ∈ R, p i) ≤ Q := fun _ hR => (Finset.mem_filter.mp hR).2
  have hbound := prime_subset_main_term publishedAdditiveLargeSieve p hc (fun i => S (p i))
    (fun i => hS _ (hmem i)) G hQ hM A hA J hGprod
    (fun _ _ x hx i _ => ha x hx (p i) (hmem i))
  have hsum : (∑ R ∈ G, ∏ i ∈ R, ((p i : ℝ) / (S (p i)).card - 1)) =
      ∑ U ∈ boundedSieveSubsets P Q, ∏ q ∈ U, ((q : ℝ) / (S q).card - 1) := by
    apply Finset.sum_bij (fun R _ => R.image p)
    · intro R hR
      have hprod : (∏ q ∈ R.image p, q) = ∏ i ∈ R, p i := by
        rw [Finset.prod_image]; exact fun _ _ _ _ he => hinj he
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro q hq
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
        exact hmem i
      · rw [hprod]
        exact hGprod R hR
    · intro R _ T _ he
      exact Finset.image_injective hinj he
    · intro U hU
      have hUP := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
      let R := (Finset.univ : Finset (Fin P.card)).filter fun i => p i ∈ U
      have himage : R.image p = U := by
        ext q
        constructor
        · intro hq
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
          exact (Finset.mem_filter.mp hi).2
        · intro hq
          obtain ⟨i, hi⟩ := hcover q (hUP hq)
          exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, by simpa only [hi] using hq⟩, hi⟩
      refine ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩, himage⟩
      have he : (∏ q ∈ U, q) = ∏ i ∈ R, p i := by
        rw [← himage, Finset.prod_image]; exact fun _ _ _ _ hij => hinj hij
      rw [← he]
      exact (Finset.mem_filter.mp hU).2
    · intro R _
      rw [Finset.prod_image]; exact fun _ _ _ _ he => hinj he
  rwa [hsum] at hbound

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftSieveBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed-shift counting sieve with its actual local weights -/

namespace Ostmann

open scoped Classical BigOperators

 theorem finiteShiftAllowed_weight (B : Finset ℕ) (p : ℕ) [NeZero p]
    (hB : ∀ b ∈ B, b < p) (hcard : B.card < p) :
    (finiteShiftAllowed B p).Nonempty ∧
      (p : ℝ) / (finiteShiftAllowed B p).card - 1 =
        (B.card : ℝ) / ((p : ℝ) - B.card) := by
  have hsum := finiteShiftAllowed_card B p hB
  have hpos : 0 < (finiteShiftAllowed B p).card := by omega
  have hposR : (0 : ℝ) < (finiteShiftAllowed B p).card := by exact_mod_cast hpos
  have hsumR : ((finiteShiftAllowed B p).card : ℝ) + B.card = p := by exact_mod_cast hsum
  have hd : (0 : ℝ) < (p : ℝ) - B.card := by linarith
  refine ⟨Finset.card_pos.mp hpos, ?_⟩
  field_simp
  nlinarith

 theorem fixed_shift_sieve_bound {M Q : ℕ} (B P : Finset ℕ)
    (hM : 1 ≤ M) (hQ : 1 ≤ Q) (A : Finset (Fin M)) (hA : A.Nonempty)
    (hP : ∀ p ∈ P, p.Prime) (hPQ : ∀ p ∈ P, p ≤ Q) (hB : ∀ p ∈ P, ∀ b ∈ B, b < p)
    (hcard : ∀ p ∈ P, B.card < p)
    (hlarge : ∀ a ∈ A, Q < a.val)
    (hprime : ∀ a ∈ A, ∀ b ∈ B, (a.val + b).Prime) :
    (∑ U ∈ boundedSieveSubsets P Q,
      ∏ p ∈ U, (B.card : ℝ) / ((p : ℝ) - B.card)) ≤
        ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  have hS (p : ℕ) (hp : p ∈ P) : (finiteShiftAllowed B p).Nonempty := by
    let : NeZero p := ⟨(hP p hp).ne_zero⟩
    exact (finiteShiftAllowed_weight B p (hB p hp)
      (hcard p hp)).1
  have h := prime_set_support_sieve P hP
    (finiteShiftAllowed B) hS hQ hM A hA 0 (by
      intro a ha p hp
      let : NeZero p := ⟨(hP p hp).ne_zero⟩
      have hpQ := hPQ p hp
      simpa only [zero_add, Int.cast_natCast] using
        finiteShiftAllowed_mem_of_prime B p a.val (hP p hp)
          (lt_of_le_of_lt hpQ (hlarge a ha)) (hprime a ha))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.prod_congr rfl
  intro p hp
  have hpP := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hp
  let : NeZero p := ⟨(hP p hpP).ne_zero⟩
  exact (finiteShiftAllowed_weight B p (hB p hpP) (hcard p hpP)).2.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftPowerCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-shift counting at integer-power sieve cutoffs -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem fixed_shift_power_count (B : Finset ℕ) (hB : B.Nonempty) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop, ∀ M : ℕ, 1 ≤ M →
      ∀ A : Finset (Fin M), A.Nonempty →
      (∀ a ∈ A, R ^ (10 * B.card) < a.val) →
      (∀ a ∈ A, ∀ b ∈ B, (a.val + b).Prime) →
      (A.card : ℝ) * Real.log (R : ℝ) ^ B.card ≤
        C * ((M : ℝ) + ((R ^ (10 * B.card) : ℕ) : ℝ) ^ 2) := by
  let p₀ := max (B.sup id) B.card
  have hj : 1 ≤ B.card := hB.card_pos
  have hjp : B.card ≤ p₀ := le_max_right _ _
  obtain ⟨c, hc, hweights⟩ := fixed_shift_weight_at_power p₀ B.card hj hjp
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  filter_upwards [hweights, eventually_ge_atTop (2 : ℕ)] with R hR hR2
  intro M hM A hA hlarge hprime
  have hRQ : R ≤ R ^ (10 * B.card) := Nat.le_self_pow (by omega) R
  have hQ : 1 ≤ R ^ (10 * B.card) := (by omega : 1 ≤ R).trans hRQ
  have hP : ∀ p ∈ fixedShiftPrimeSet p₀ R, p.Prime :=
    fun p hp => (mem_fixedShiftPrimeSet.mp hp).1
  have hPQ : ∀ p ∈ fixedShiftPrimeSet p₀ R, p ≤ R ^ (10 * B.card) :=
    fun p hp => (mem_fixedShiftPrimeSet.mp hp).2.2.trans hRQ
  have hb : ∀ p ∈ fixedShiftPrimeSet p₀ R, ∀ b ∈ B, b < p := by
    intro p hp b hb
    have hb0 : b ≤ p₀ := (Finset.le_sup (f := id) hb).trans (le_max_left _ _)
    exact hb0.trans_lt (mem_fixedShiftPrimeSet.mp hp).2.1
  have hbc : ∀ p ∈ fixedShiftPrimeSet p₀ R, B.card < p :=
    fun p hp => hjp.trans_lt (mem_fixedShiftPrimeSet.mp hp).2.1
  have hsieve := fixed_shift_sieve_bound B (fixedShiftPrimeSet p₀ R) hM hQ A hA
    hP hPQ hb hbc hlarge hprime
  have hbound := hR.trans hsieve
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hmul := (le_div_iff₀ hAc).mp hbound
  rw [mul_comm c⁻¹ _, ← div_eq_mul_inv]
  apply (le_div_iff₀ hc).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftRootCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer-root cutoffs for fixed-shift sieving on arbitrary intervals -/

namespace Ostmann

open Filter

 theorem nthRoot_tendsto (k : ℕ) (hk : k ≠ 0) :
    Tendsto (Nat.nthRoot k) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b ^ k)] with N hN
  exact (Nat.le_nthRoot_iff hk).mpr hN

 theorem nthRoot_log_comparison (k N : ℕ) (hk : k ≠ 0) (hN : 2 ≤ N)
    (hR : 2 ≤ Nat.nthRoot k N) :
    Real.log (N : ℝ) ≤ 2 * (k : ℝ) * Real.log (Nat.nthRoot k N : ℝ) := by
  let R := Nat.nthRoot k N
  have hRp : (0 : ℝ) < R := by dsimp [R]; exact_mod_cast (by omega : 0 < Nat.nthRoot k N)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hupper : (N : ℝ) ≤ ((R + 1 : ℕ) : ℝ) ^ k := by
    exact_mod_cast (Nat.lt_pow_nthRoot_add_one hk N).le
  have hl := Real.log_le_log hNp hupper
  rw [Real.log_pow] at hl
  have hrbound : ((R + 1 : ℕ) : ℝ) ≤ 2 * (R : ℝ) := by
    push_cast
    have hh : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hrlog := Real.log_le_log (by positivity : (0 : ℝ) < (R + 1 : ℕ)) hrbound
  rw [Real.log_mul (by norm_num) hRp.ne'] at hrlog
  have h2log := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ R by exact_mod_cast hR)
  change Real.log (N : ℝ) ≤ 2 * (k : ℝ) * Real.log (R : ℝ)
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

 theorem fixedShiftRoot_square_cutoff (j N : ℕ) (hj : 1 ≤ j) :
    (Nat.nthRoot (20 * j) N ^ (10 * j)) ^ 2 ≤ N := by
  rw [← pow_mul]
  rw [show 10 * j * 2 = 20 * j by omega]
  exact Nat.pow_nthRoot_le (Or.inl (by omega : 20 * j ≠ 0))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSupportEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A missing-residue lower bound for the actual reduced prime energy -/

namespace Ostmann

open scoped Classical BigOperators

 theorem unitFrequencyEnergy_int_congr {q r : ℕ} [NeZero q] [NeZero r]
    (h : q = r) {ι : Type*} (A : Finset ι) (a : ι → ℤ) :
    unitFrequencyEnergy A (fun x => (a x : ZMod q)) =
      unitFrequencyEnergy A (fun x => (a x : ZMod r)) := by
  subst r
  rfl

 theorem prime_support_energy_lower {ι : Type*} (p : ℕ) [Fact p.Prime]
    (A : Finset ι) (hA : A.Nonempty) (a : ι → ℤ)
    (S : Finset (ZMod p)) (hS : S.Nonempty)
    (ha : ∀ x ∈ A, (a x : ZMod p) ∈ S) :
    (p : ℝ) / S.card - 1 ≤ unitFrequencyEnergy A (fun x => (a x : ZMod p)) := by
  let ps : Fin 1 → ℕ := fun _ => p
  let ss : ∀ i, Finset (ZMod (ps i)) := fun _ => S
  let R : Finset (Fin 1) := {0}
  have hc : Pairwise (fun i j => (ps i).Coprime (ps j)) := by
    intro i j hij
    have he : i = j := Subsingleton.elim i j
    exact (hij he).elim
  have hprod : ∏ i ∈ R, ps i = p := by simp [R, ps]
  let : NeZero (∏ i ∈ R, ps i) := ⟨by rw [hprod]; exact (Fact.out : p.Prime).ne_zero⟩
  have hpa : ∀ x ∈ A, ∀ i ∈ R, (a x : ZMod (ps i)) ∈ ss i := by
    intro x hx i _
    exact ha x hx
  have he := subset_reduced_energy_expansion ps ss R hc A a hpa
  have hnonneg (T : Finset (Fin 1)) (hT : T ∈ R.powerset) :
      0 ≤ subsetSieveCoefficient ps ss R T *
        centeredSubsetEnergy ps ss T A (fun x i => (a x : ZMod (ps i))) := by
    apply mul_nonneg
    · exact subsetSieveCoefficient_nonneg ps ss R T (fun _ _ => hS)
    · exact centeredSubsetEnergy_nonneg ps ss T A _
  have hle := Finset.single_le_sum hnonneg (show ∅ ∈ R.powerset by simp)
  rw [centeredSubsetEnergy_empty ps ss A hA, mul_one] at hle
  have hcoeff : subsetSieveCoefficient ps ss R ∅ = (p : ℝ) / S.card - 1 := by
    simp [subsetSieveCoefficient, R, ps, ss]
  rw [hcoeff, ← he] at hle
  rw [unitFrequencyEnergy_int_congr hprod A a] at hle
  exact hle

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSupportSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-support sieve estimate for the summand-size argument -/

namespace Ostmann

open scoped Classical BigOperators

 theorem full_support_prime_energy {M : ℕ} (B : Set ℕ) (U : Finset (Fin M))
    (hU : U.Nonempty) (p : ℕ) [Fact p.Prime]
    (havoid : ∀ a ∈ U, (a.val : ZMod p) ∉ negativeOccupiedResidues B p) :
    ((occupiedResidues B p).card : ℝ) / p ≤ intervalSetReducedEnergy U 0 p := by
  have hmem : ∀ a ∈ U, ((a.val : ℤ) : ZMod p) ∈ allowedSummandResidues B p := by
    intro a ha
    simpa only [allowedSummandResidues, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Int.cast_natCast] using havoid a ha
  have hS : (allowedSummandResidues B p).Nonempty := by
    obtain ⟨a, ha⟩ := hU
    exact ⟨_, hmem a ha⟩
  have hlower := prime_support_energy_lower p U hU (fun a => (a.val : ℤ))
    (allowedSummandResidues B p) hS hmem
  have h := (occupied_to_allowed_ratio B p hS).trans hlower
  simpa only [intervalSetReducedEnergy_eq_unitFrequencyEnergy, zero_add] using h

 theorem full_support_prime_sieve {M Q : ℕ} (B : Set ℕ) (U : Finset (Fin M))
    (hU : U.Nonempty) (hM : 1 ≤ M) (hQ : 1 ≤ Q) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPQ : ∀ p ∈ P, p ≤ Q)
    (havoid : ∀ p ∈ P, ∀ a ∈ U, (a.val : ZMod p) ∉ negativeOccupiedResidues B p) :
    (∑ p ∈ P, ((occupiedResidues B p).card : ℝ) / p) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / U.card := by
  calc
    _ ≤ ∑ p ∈ P, intervalSetReducedEnergy U 0 p := by
      apply Finset.sum_le_sum
      intro p hp
      let : Fact p.Prime := ⟨hP p hp⟩
      exact full_support_prime_energy B U hU p (havoid p hp)
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, intervalSetReducedEnergy U 0 q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Finset.mem_Icc.mpr ⟨(hP p hp).one_le, hPQ p hp⟩
      · intro q _ _
        exact intervalSetReducedEnergy_nonneg U 0 q
    _ ≤ _ := additiveSieve_probability_bound publishedAdditiveLargeSieve hM hQ U hU 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_NaturalPrimeSupportSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The support sieve for actual natural-number summand tails -/

namespace Ostmann

open scoped Classical BigOperators

 theorem mem_naturalIntervalSet {S : Finset ℕ} {N : ℕ} {a : Fin (N + 1)} :
    a ∈ naturalIntervalSet S N ↔ a.val ∈ S := by simp [naturalIntervalSet]

 theorem naturalIntervalSet_card (S : Finset ℕ) (N : ℕ) (hS : ∀ a ∈ S, a ≤ N) :
    (naturalIntervalSet S N).card = S.card := by
  apply Finset.card_bij (fun a _ => a.val)
  · intro a ha
    exact mem_naturalIntervalSet.mp ha
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro a ha
    exact ⟨⟨a, by have := hS a ha; omega⟩, mem_naturalIntervalSet.mpr ha, rfl⟩

 theorem natural_full_support_prime_sieve (B : Set ℕ) (S P : Finset ℕ)
    (N Q : ℕ) (hS : S.Nonempty) (hbound : ∀ a ∈ S, a ≤ N) (hQ : 1 ≤ Q)
    (hP : ∀ p ∈ P, p.Prime) (hPQ : ∀ p ∈ P, p ≤ Q)
    (havoid : ∀ p ∈ P, ∀ a ∈ S, (a : ZMod p) ∉ negativeOccupiedResidues B p) :
    (∑ p ∈ P, ((occupiedResidues B p).card : ℝ) / p) ≤
      (((N + 1 : ℕ) : ℝ) + (Q : ℝ) ^ 2) / S.card := by
  have hcard := naturalIntervalSet_card S N hbound
  have hU : (naturalIntervalSet S N).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact hS.card_pos
  have h := full_support_prime_sieve B (naturalIntervalSet S N) hU (by omega) hQ P hP hPQ
    (fun p hp a ha => havoid p hp a.val (mem_naturalIntervalSet.mp ha))
  simpa only [hcard] using h

 theorem EventuallyPrimeSumset.tail_full_support_prime_sieve {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N₀ : ℕ, ∀ X Q : ℕ, ∀ P : Finset ℕ, 1 ≤ Q →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ Q) →
      (summandTail A (N₀ + Q) X).Nonempty →
      (∑ p ∈ P, ((occupiedResidues B p).card : ℝ) / p) ≤
        (((X + 1 : ℕ) : ℝ) + (Q : ℝ) ^ 2) / (summandTail A (N₀ + Q) X).card := by
  obtain ⟨N₀, hN⟩ := h.full_residue_avoidance
  refine ⟨N₀, ?_⟩
  intro X Q P hQ hP hPQ hU
  refine natural_full_support_prime_sieve B (summandTail A (N₀ + Q) X) P X Q hU ?_ hQ hP hPQ ?_
  · intro a ha
    exact (mem_summandTail A (N₀ + Q) X a).mp ha |>.2.2
  · intro p hp a ha
    obtain ⟨haA, hlarge, _⟩ := (mem_summandTail A (N₀ + Q) X a).mp ha
    exact hN p (hP p hp) a haA (by have := hPQ p hp; omega)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftTailCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed-shift sieve bound at every sufficiently large endpoint -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem fixed_shift_tail_count (B : Finset ℕ) (hB : B.Nonempty) (C : Set ℕ)
    (N₀ : ℕ) (hprime : ∀ a ∈ C, N₀ ≤ a → ∀ b ∈ B, (a + b).Prime) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop,
      let Q := Nat.nthRoot (20 * B.card) N ^ (10 * B.card)
      ((summandTail C (Q + N₀) N).card : ℝ) * Real.log (N : ℝ) ^ B.card ≤ D * N := by
  obtain ⟨D, hD, hcount⟩ := fixed_shift_power_count B hB
  let k := 20 * B.card
  have hk : k ≠ 0 := by dsimp [k]; have := hB.card_pos; omega
  let F : ℝ := (2 * (k : ℝ)) ^ B.card
  have hF : 0 < F := by dsimp [F]; exact pow_pos (by exact_mod_cast (by omega : 0 < 2 * k)) _
  refine ⟨3 * F * D, by positivity, ?_⟩
  have hRcount := (nthRoot_tendsto k hk).eventually hcount
  have hRlarge := (nthRoot_tendsto k hk).eventually (eventually_ge_atTop 2)
  filter_upwards [hRcount, hRlarge, eventually_ge_atTop (2 : ℕ)] with N hN hR hN2
  dsimp only
  let R := Nat.nthRoot k N
  let Q := R ^ (10 * B.card)
  let U := summandTail C (Q + N₀) N
  have hNU : ∀ a ∈ U, a ≤ N := fun a ha => (mem_summandTail C (Q + N₀) N a).mp ha |>.2.2
  let V := naturalIntervalSet U N
  have hcard : V.card = U.card := naturalIntervalSet_card U N hNU
  have hQsq : Q ^ 2 ≤ N := fixedShiftRoot_square_cutoff B.card N hB.card_pos
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R))
  have hlog := nthRoot_log_comparison k N hk hN2 hR
  have hpow := pow_le_pow_left₀ hlogN hlog B.card
  rw [mul_pow] at hpow
  change Real.log (N : ℝ) ^ B.card ≤ F * Real.log (R : ℝ) ^ B.card at hpow
  by_cases hU : U.Nonempty
  · have hV : V.Nonempty := by rw [← Finset.card_pos, hcard]; exact hU.card_pos
    have hb := hN (N + 1) (by omega) V hV (by
      intro a ha
      have := (mem_summandTail C (Q + N₀) N a.val).mp (mem_naturalIntervalSet.mp ha)
      change Q < a.val
      omega) (by
      intro a ha b hb
      obtain ⟨haC, hlarge, _⟩ := (mem_summandTail C (Q + N₀) N a.val).mp
        (mem_naturalIntervalSet.mp ha)
      exact hprime a.val haC (by omega) b hb)
    rw [hcard] at hb
    change (U.card : ℝ) * Real.log (R : ℝ) ^ B.card ≤ D *
      (((N + 1 : ℕ) : ℝ) + (Q : ℝ) ^ 2) at hb
    have hsquare : (Q : ℝ) ^ 2 ≤ N := by exact_mod_cast hQsq
    have hb' : (U.card : ℝ) * Real.log (R : ℝ) ^ B.card ≤ D * (3 * (N : ℝ)) := by
      have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      push_cast at hb
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (α := ℝ) U.card)
    have hf := mul_le_mul_of_nonneg_left hb' hF.le
    change (U.card : ℝ) * Real.log (N : ℝ) ^ B.card ≤ _
    nlinarith
  · have hzero : U.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hU)
    change (U.card : ℝ) * Real.log (N : ℝ) ^ B.card ≤ _
    rw [hzero, Nat.cast_zero, zero_mul]
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FixedShiftCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-shift counting, manuscript Lemma 2.1

The proof uses the proved additive sieve, exact missing-class weights, Mertens
bounds, and integer-root cutoffs. All removed initial points are restored.
-/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem fixed_shift_count (B : Finset ℕ) (hB : B.Nonempty) (C : Set ℕ)
    (N₀ : ℕ) (hprime : ∀ a ∈ C, N₀ ≤ a → ∀ b ∈ B, (a + b).Prime) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ N : ℕ in atTop,
      ((summandPrefix C N).card : ℝ) ≤ E * N / Real.log (N : ℝ) ^ B.card := by
  obtain ⟨D, hD, htail⟩ := fixed_shift_tail_count B hB C N₀ hprime
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    (sqrt_log_power_initial_small B.card (N₀ : ℝ) (Nat.cast_nonneg N₀))
  refine ⟨D + 1, by positivity, ?_⟩
  filter_upwards [htail, hsmall, eventually_ge_atTop (2 : ℕ)] with N ht hs hN
  let Q := Nat.nthRoot (20 * B.card) N ^ (10 * B.card)
  change ((summandTail C (Q + N₀) N).card : ℝ) * Real.log (N : ℝ) ^ B.card ≤ D * N at ht
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hQsq : Q ^ 2 ≤ N := fixedShiftRoot_square_cutoff B.card N hB.card_pos
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hQsq
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hL : 0 < Real.log (N : ℝ) ^ B.card := pow_pos hl _
  have hremoved : ((Q : ℝ) + N₀ + 1) * Real.log (N : ℝ) ^ B.card ≤ N := by
    calc
      _ ≤ (Real.sqrt (N : ℝ) + N₀ + 1) * Real.log (N : ℝ) ^ B.card := by
        gcongr
      _ ≤ _ := hs
  have hcard : ((summandPrefix C N).card : ℝ) ≤
      ((Q : ℝ) + N₀ + 1) + (summandTail C (Q + N₀) N).card := by
    exact_mod_cast summandPrefix_card_le_initial_add_tail C (Q + N₀) N
  have hm := mul_le_mul_of_nonneg_right hcard hL.le
  apply (le_div_iff₀ hL).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandLogarithmicUpper
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every fixed logarithmic saving for an infinite summand -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_logarithmic_upper {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Infinite) (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ((summandPrefix A N).card : ℝ) ≤ C * N / Real.log (N : ℝ) ^ j := by
  obtain ⟨T, hTB, hcard⟩ := hB.exists_subset_card_eq j
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨N₀, hN⟩ := h.prime_add
  obtain ⟨C, hC, hbound⟩ := fixed_shift_count T hT A N₀ (by
    intro a ha hNa b hb
    exact hN a ha b (hTB hb) (by omega))
  refine ⟨C, hC, ?_⟩
  simpa only [hcard] using hbound

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandLogarithmicLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every fixed logarithmic power is a lower bound for either summand -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_logarithmic_lower {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.log (N : ℝ) ^ k ≤ ((summandPrefix A N).card : ℝ) := by
  obtain ⟨C, hC, hupper⟩ := h.symm.summand_logarithmic_upper hA (k + 1) (by omega)
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  filter_upwards [hupper, h.coverage_product_lower, eventually_ge_atTop (2 : ℕ)]
    with N hu hl hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  let a : ℝ := (summandPrefix A N).card
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hx : (N : ℝ) / (4 * Real.log (N : ℝ)) ≤
      a * (C * N / Real.log (N : ℝ) ^ (k + 1)) :=
    hl.trans (mul_le_mul_of_nonneg_left hu ha)
  simp only [← mul_div_assoc] at hx
  have hy := (div_le_div_iff₀ (by positivity : 0 < 4 * Real.log (N : ℝ))
    (pow_pos hlog (k + 1))).mp hx
  have hz : ((N : ℝ) * Real.log (N : ℝ)) * Real.log (N : ℝ) ^ k ≤
      ((N : ℝ) * Real.log (N : ℝ)) * (4 * C * a) := by
    calc
      _ = (N : ℝ) * Real.log (N : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ _ := hy
      _ = _ := by ring
  have hh := (mul_le_mul_iff_right₀ (mul_pos hNp hlog)).mp hz
  change (1 / (4 * C)) * Real.log (N : ℝ) ^ k ≤ a
  rw [one_div, inv_mul_eq_div]
  exact (div_le_iff₀ (by positivity : 0 < 4 * C)).mpr (by nlinarith [hh])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExponentialSampling
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential cutoffs for the two-length summand comparison -/

namespace Ostmann

open Filter

 theorem exponentialSample_tendsto : Tendsto exponentialSample atTop atTop :=
  tendsto_nat_ceil_atTop.comp (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop)

 theorem exponentialSample_log (t : ℕ) :
    (t : ℝ) ≤ Real.log (exponentialSample t : ℝ) ∧
      Real.log (exponentialSample t : ℝ) ≤ t + 1 := by
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
  have he : 1 ≤ Real.exp (t : ℝ) := Real.one_le_exp ht
  have hlo : Real.exp (t : ℝ) ≤ (exponentialSample t : ℝ) := Nat.le_ceil _
  have hhi : (exponentialSample t : ℝ) ≤ 2 * Real.exp (t : ℝ) := by
    have hh := (Nat.ceil_lt_add_one (Real.exp_pos (t : ℝ)).le).le
    change (exponentialSample t : ℝ) ≤ _ at hh
    linarith
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hlo
  · have hh := Real.log_le_log ((Real.exp_pos _).trans_le hlo) hhi
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith

 theorem EventuallyPrimeSumset.exponential_sample_population {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Infinite) :
    ∀ᶠ t : ℕ in atTop,
      1 ≤ exponentialSample t ∧ (summandPrefix B (exponentialSample t)).Nonempty ∧
      3 * (t : ℝ) ^ 6 ≤ ((summandPrefix B (exponentialSample t)).card : ℝ) := by
  obtain ⟨c, hc, hpop⟩ := h.symm.summand_logarithmic_lower hB 12
  have hlarge := ((tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (3 / c))
  filter_upwards [exponentialSample_tendsto.eventually hpop, hlarge,
    eventually_ge_atTop (1 : ℕ)] with t hp ht ht1
  have htp : 0 < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hlog := (exponentialSample_log t).1
  have hpow : (t : ℝ) ^ 12 ≤ Real.log (exponentialSample t : ℝ) ^ 12 := by gcongr
  change 3 / c ≤ (t : ℝ) ^ 6 at ht
  have hmult : 3 ≤ c * (t : ℝ) ^ 6 := by
    have hh := (div_le_iff₀ hc).mp ht
    nlinarith
  have hcount : 3 * (t : ℝ) ^ 6 ≤ ((summandPrefix B (exponentialSample t)).card : ℝ) := by
    calc
      _ ≤ c * (t : ℝ) ^ 12 := by nlinarith [mul_le_mul_of_nonneg_right hmult (pow_nonneg htp.le 6)]
      _ ≤ c * Real.log (exponentialSample t : ℝ) ^ 12 := mul_le_mul_of_nonneg_left hpow hc.le
      _ ≤ _ := hp
  have hne : (summandPrefix B (exponentialSample t)).Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < (summandPrefix B (exponentialSample t)).card :=
      (by positivity : 0 < 3 * (t : ℝ) ^ 6).trans_le hcount
    exact_mod_cast hh
  have hsample : 1 ≤ exponentialSample t := by
    have hh : (0 : ℝ) < (exponentialSample t : ℝ) :=
      (Real.exp_pos _).trans_le (Nat.le_ceil _)
    have hh' : 0 < exponentialSample t := by exact_mod_cast hh
    omega
  exact ⟨hsample, hne, hcount⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_ReciprocalSupportCauchy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reciprocal-support Cauchy estimate in Elsholtz's size argument -/

namespace Ostmann

open scoped Classical BigOperators

 theorem reciprocal_sum_cauchy {ι : Type*} (P : Finset ι) (v : ι → ℝ)
    (hv : ∀ p ∈ P, 0 < v p) :
    (P.card : ℝ) ^ 2 ≤ (∑ p ∈ P, v p) * ∑ p ∈ P, 1 / v p := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun p => Real.sqrt (v p)) (fun p => (Real.sqrt (v p))⁻¹)
  have hprod : (∑ p ∈ P, Real.sqrt (v p) * (Real.sqrt (v p))⁻¹) = (P.card : ℝ) := by
    calc
      _ = ∑ _p ∈ P, (1 : ℝ) := Finset.sum_congr rfl (fun p hp => mul_inv_cancel₀
        (Real.sqrt_pos.mpr (hv p hp)).ne')
      _ = _ := by simp
  have hs : (∑ p ∈ P, Real.sqrt (v p) ^ 2) = ∑ p ∈ P, v p :=
    Finset.sum_congr rfl (fun p hp => Real.sq_sqrt (hv p hp).le)
  have hi : (∑ p ∈ P, (Real.sqrt (v p))⁻¹ ^ 2) = ∑ p ∈ P, 1 / v p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [inv_pow, Real.sq_sqrt (hv p hp).le, one_div]
  rwa [hprod, hs, hi] at hc

 theorem occupied_support_cauchy (B : Set ℕ) (hB : B.Nonempty) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (Q K ell : ℝ) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hell : 0 ≤ ell) (hpQ : ∀ p ∈ P, (p : ℝ) ≤ Q)
    (hlog : ∀ p ∈ P, ell ≤ Real.log (p : ℝ))
    (hsieve : (∑ p ∈ P, ((occupiedResidues B p).card : ℝ) / p) ≤ K) :
    ell * (P.card : ℝ) ^ 2 ≤ Q * K *
      ∑ p ∈ P, Real.log (p : ℝ) / ((occupiedResidues B p).card : ℝ) := by
  let v : ℕ → ℝ := fun p => (occupiedResidues B p).card
  have hv : ∀ p ∈ P, 0 < v p := by
    intro p hp
    dsimp [v]
    exact_mod_cast (occupiedResidues_nonempty hB (hP p hp).pos).card_pos
  have hvc : (∑ p ∈ P, v p) ≤ Q * K := by
    calc
      _ ≤ ∑ p ∈ P, Q * (v p / p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
        rw [← mul_div_assoc]
        exact (le_div_iff₀ hp').mpr (by nlinarith [hv p hp, hpQ p hp])
      _ = Q * (∑ p ∈ P, v p / p) := (Finset.mul_sum _ _ _).symm
      _ ≤ Q * K := mul_le_mul_of_nonneg_left hsieve hQ
  have hinv : 0 ≤ ∑ p ∈ P, 1 / v p :=
    Finset.sum_nonneg (fun p hp => div_nonneg zero_le_one (hv p hp).le)
  have hweight : ell * (∑ p ∈ P, 1 / v p) ≤
      ∑ p ∈ P, Real.log (p : ℝ) / v p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (hlog p hp) (hv p hp).le
  calc
    _ ≤ ell * ((∑ p ∈ P, v p) * ∑ p ∈ P, 1 / v p) :=
      mul_le_mul_of_nonneg_left (reciprocal_sum_cauchy P v hv) hell
    _ ≤ ell * ((Q * K) * ∑ p ∈ P, 1 / v p) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvc hinv) hell
    _ = Q * K * (ell * ∑ p ∈ P, 1 / v p) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (mul_nonneg hQ hK)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandSizeFiniteInequality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite sieve/collision inequality underlying the square-root bounds

The prime set and the second sampling length are independent. This retains the
freedom to choose a very long second prefix in the subpower bootstrap.
-/

namespace Ostmann

open scoped Classical BigOperators

 theorem EventuallyPrimeSumset.summand_size_finite_inequality {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Nonempty) :
    ∃ N₀ : ℕ, ∀ X Q Y : ℕ, ∀ P : Finset ℕ, ∀ ell : ℝ,
      1 ≤ Q → 1 ≤ Y → 0 ≤ ell →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ Q) →
      (∀ p ∈ P, ell ≤ Real.log (p : ℝ)) →
      (summandTail A (N₀ + Q) X).Nonempty → (summandPrefix B Y).Nonempty →
      ((summandTail A (N₀ + Q) X).card : ℝ) * (ell * (P.card : ℝ) ^ 2) ≤
        (Q : ℝ) * (((X + 1 : ℕ) : ℝ) + (Q : ℝ) ^ 2) *
          (Real.log (Y : ℝ) + (1 / ((summandPrefix B Y).card : ℝ)) *
            ∑ p ∈ P, Real.log (p : ℝ)) := by
  obtain ⟨N₀, hN⟩ := h.tail_full_support_prime_sieve
  refine ⟨N₀, ?_⟩
  intro X Q Y P ell hQ hY hell hP hPQ hlog hU hV
  let m : ℝ := (summandTail A (N₀ + Q) X).card
  let R : ℝ := ((X + 1 : ℕ) : ℝ) + (Q : ℝ) ^ 2
  let H : ℝ := ∑ p ∈ P, Real.log (p : ℝ) / ((occupiedResidues B p).card : ℝ)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast hU.card_pos
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hq : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hcs := occupied_support_cauchy B hB P hP (Q : ℝ) (R / m) ell hq
    (div_nonneg hR hm.le) hell (fun p hp => by exact_mod_cast hPQ p hp) hlog
    (hN X Q P hQ hP hPQ hU)
  have hcol := summandPrefix_occupied_bound B P Y hY hV hP
  have hmcs := mul_le_mul_of_nonneg_left hcs hm.le
  have heq : m * ((Q : ℝ) * (R / m) * H) = (Q : ℝ) * R * H := by
    field_simp
  change m * (ell * (P.card : ℝ) ^ 2) ≤ _
  change m * (ell * (P.card : ℝ) ^ 2) ≤ m * ((Q : ℝ) * (R / m) * H) at hmcs
  rw [heq] at hmcs
  exact hmcs.trans (mul_le_mul_of_nonneg_left hcol (mul_nonneg hq hR))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandSquareComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A two-cutoff comparison at square endpoints -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

private theorem square_comparison_algebra (q L m c H : ℝ)
    (hq : 1 ≤ q) (hL : 0 < L) (hm : 0 ≤ m) (_hc : 0 ≤ c) (hH : 0 ≤ H)
    (hcount : q / (4 * L) ≤ c)
    (hineq : m * (L / 2 * c ^ 2) ≤ 2 * q * (q ^ 2 + 1 + (2 * q) ^ 2) * H) :
    m ≤ 384 * q * L * H := by
  have hqc : q ≤ 4 * L * c := by
    have hh := (div_le_iff₀ (by positivity : 0 < 4 * L)).mp hcount
    nlinarith
  have hsq : q ^ 2 ≤ 16 * L ^ 2 * c ^ 2 := by nlinarith
  have hmsq := mul_le_mul_of_nonneg_left hsq hm
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have hupper : m * (L / 2 * c ^ 2) ≤ 12 * q ^ 3 * H := by
    apply hineq.trans
    nlinarith [mul_nonneg (sub_nonneg.mpr hq2) (mul_nonneg (by linarith : 0 ≤ q) hH)]
  have hscaled := mul_le_mul_of_nonneg_left hupper (show 0 ≤ 32 * L by positivity)
  have hfinal : q ^ 2 * m ≤ q ^ 2 * (384 * q * L * H) := by nlinarith [hmsq, hscaled]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < q ^ 2)).mp hfinal

 theorem EventuallyPrimeSumset.summand_square_comparison {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Nonempty) :
    ∃ N₀ : ℕ, ∀ᶠ q : ℕ in atTop, ∀ Y : ℕ, 1 ≤ Y →
      (summandPrefix B Y).Nonempty →
      ((summandPrefix A (q ^ 2)).card : ℝ) ≤ N₀ + 2 * q + 1 +
        384 * q * Real.log (2 * (q : ℝ)) *
          (Real.log (Y : ℝ) + 3 * q / ((summandPrefix B Y).card : ℝ)) := by
  obtain ⟨N₀, hN⟩ := h.summand_size_finite_inequality hB
  refine ⟨N₀, ?_⟩
  filter_upwards [sizePrimeBand_eventual_bounds] with q hq
  intro Y hY hBY
  let L := Real.log (2 * (q : ℝ))
  let H := Real.log (Y : ℝ) + 3 * q / ((summandPrefix B Y).card : ℝ)
  have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have hH : 0 ≤ H := by
    dsimp [H]
    exact add_nonneg (Real.log_nonneg (by exact_mod_cast hY)) (by positivity)
  have htail : ((summandTail A (N₀ + 2 * q) (q ^ 2)).card : ℝ) ≤
      384 * q * L * H := by
    by_cases hu : (summandTail A (N₀ + 2 * q) (q ^ 2)).Nonempty
    · have he : L / 2 ≤ Real.log (q : ℝ) := by
        have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (show (2 : ℝ) ≤ q by exact_mod_cast hq.1)
        dsimp [L]
        rw [Real.log_mul (by norm_num) hqp.ne']
        linarith
      have hh := hN (q ^ 2) (2 * q) Y (sizePrimeBand q) (L / 2)
        (by omega) hY (by positivity)
        (fun p hp => (mem_sizePrimeBand.mp hp).1)
        (fun p hp => (mem_sizePrimeBand.mp hp).2.2)
        (fun p hp => he.trans (Real.log_le_log hqp
          (by exact_mod_cast (mem_sizePrimeBand.mp hp).2.1.le))) hu hBY
      have hmass : Real.log (Y : ℝ) +
          (1 / ((summandPrefix B Y).card : ℝ)) *
            (∑ p ∈ sizePrimeBand q, Real.log (p : ℝ)) ≤ H := by
        have hh := mul_le_mul_of_nonneg_left hq.2.2
          (show 0 ≤ 1 / ((summandPrefix B Y).card : ℝ) by positivity)
        dsimp [H]
        simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc, add_comm] using add_le_add_left hh (Real.log (Y : ℝ))
      have hi : ((summandTail A (N₀ + 2 * q) (q ^ 2)).card : ℝ) *
          (L / 2 * ((sizePrimeBand q).card : ℝ) ^ 2) ≤
          2 * q * ((q : ℝ) ^ 2 + 1 + (2 * q) ^ 2) * H := by
        push_cast at hh
        exact hh.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
      exact square_comparison_algebra q L _ _ H hq1 hL (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) hH hq.2.1 hi
    · rw [Finset.not_nonempty_iff_eq_empty.mp hu, Finset.card_empty, Nat.cast_zero]
      positivity
  have hc : ((summandPrefix A (q ^ 2)).card : ℝ) ≤
      (N₀ : ℝ) + 2 * q + 1 + ((summandTail A (N₀ + 2 * q) (q ^ 2)).card : ℝ) := by
    exact_mod_cast summandPrefix_card_le_initial_add_tail A (N₀ + 2 * q) (q ^ 2)
  exact hc.trans (add_le_add_right htail _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandPolynomialBootstrap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete polynomial bootstrap for summand counts

The second sampling length is exponential. Only the integer powers 6, 8 and
12 are needed; a general subpower theorem is unnecessary for this application.
-/

namespace Ostmann

open Filter

 theorem constant_log_linear_small (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, C * (1 + Real.log x) ≤ x := by
  have hs := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).const_mul_left C).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hs, eventually_ge_atTop (max 1 (2 * C))] with x hx hxl
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hxl
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hh : C * Real.log x ≤ x / 2 := by
    simpa only [Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC hlog), abs_of_nonneg hx0,
      one_div, div_eq_mul_inv, one_mul, mul_comm] using hx
  have hlarge := (le_max_right 1 (2 * C)).trans hxl
  nlinarith

 theorem EventuallyPrimeSumset.summand_polynomial_bootstrap {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Infinite) :
    ∀ᶠ t : ℕ in atTop,
      ((summandPrefix A (t ^ 12)).card : ℝ) ≤ (t : ℝ) ^ 8 := by
  obtain ⟨N₀, hcomp⟩ := h.summand_square_comparison hB.nonempty
  let K : ℝ := N₀ + 8067
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsmall := tendsto_natCast_atTop_atTop.eventually (constant_log_linear_small K hK)
  have htend : Tendsto (fun t : ℕ => t ^ 6) atTop atTop := tendsto_pow_atTop (by norm_num)
  filter_upwards [htend.eventually hcomp, h.exponential_sample_population hB,
    hsmall, eventually_ge_atTop (2 : ℕ)] with t hc hp hs ht
  have htp : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
  have hlog : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg ht1
  have hlog6 : Real.log (2 * ((t ^ 6 : ℕ) : ℝ)) ≤ 7 * Real.log (t : ℝ) := by
    have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ t by exact_mod_cast ht)
    rw [Nat.cast_pow, Real.log_mul (by norm_num) (pow_pos htp 6).ne', Real.log_pow]
    norm_num
    linarith
  have hfrac : 3 * ((t ^ 6 : ℕ) : ℝ) /
      ((summandPrefix B (exponentialSample t)).card : ℝ) ≤ 1 := by
    have hcard : (0 : ℝ) < (summandPrefix B (exponentialSample t)).card :=
      by exact_mod_cast hp.2.1.card_pos
    apply (div_le_iff₀ hcard).mpr
    simpa only [Nat.cast_pow, one_mul] using hp.2.2
  have hbound := hc (exponentialSample t) hp.1 hp.2.1
  have hlogY := (exponentialSample_log t).2
  have hsum : Real.log (exponentialSample t : ℝ) +
      3 * ((t ^ 6 : ℕ) : ℝ) / ((summandPrefix B (exponentialSample t)).card : ℝ) ≤
        3 * (t : ℝ) := by linarith
  have hsum0 : 0 ≤ Real.log (exponentialSample t : ℝ) +
      3 * ((t ^ 6 : ℕ) : ℝ) / ((summandPrefix B (exponentialSample t)).card : ℝ) := by
    have := (exponentialSample_log t).1
    positivity
  have hmain : 384 * ((t ^ 6 : ℕ) : ℝ) * Real.log (2 * ((t ^ 6 : ℕ) : ℝ)) *
      (Real.log (exponentialSample t : ℝ) +
        3 * ((t ^ 6 : ℕ) : ℝ) / ((summandPrefix B (exponentialSample t)).card : ℝ)) ≤
          8064 * (t : ℝ) ^ 7 * Real.log (t : ℝ) := by
    calc
      _ ≤ 384 * ((t ^ 6 : ℕ) : ℝ) * (7 * Real.log (t : ℝ)) * (3 * (t : ℝ)) := by
        gcongr
      _ = _ := by push_cast; ring
  have ht6 : (1 : ℝ) ≤ (t : ℝ) ^ 6 := one_le_pow₀ ht1
  have ht67 : (t : ℝ) ^ 6 ≤ (t : ℝ) ^ 7 := by
    simpa only [pow_succ] using le_mul_of_one_le_right (pow_nonneg htp.le 6) ht1
  have hboundary : (N₀ : ℝ) + 2 * ((t ^ 6 : ℕ) : ℝ) + 1 ≤ K * (t : ℝ) ^ 7 := by
    have hfirst : (N₀ : ℝ) + 2 * (t : ℝ) ^ 6 + 1 ≤ (N₀ + 3 : ℝ) * (t : ℝ) ^ 6 := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N₀) (sub_nonneg.mpr ht6)]
    push_cast
    calc
      _ ≤ (N₀ + 3 : ℝ) * (t : ℝ) ^ 6 := hfirst
      _ ≤ (N₀ + 3 : ℝ) * (t : ℝ) ^ 7 := mul_le_mul_of_nonneg_left ht67 (by positivity)
      _ ≤ K * (t : ℝ) ^ 7 := by dsimp [K]; gcongr; norm_num
  have hmainK : 8064 * (t : ℝ) ^ 7 * Real.log (t : ℝ) ≤
      K * (t : ℝ) ^ 7 * Real.log (t : ℝ) := by
    dsimp [K]
    gcongr
    have := Nat.cast_nonneg (α := ℝ) N₀
    linarith
  have hfinal : ((summandPrefix A (t ^ 12)).card : ℝ) ≤
      K * (t : ℝ) ^ 7 * (1 + Real.log (t : ℝ)) := by
    have hb : ((summandPrefix A (t ^ 12)).card : ℝ) ≤
        (N₀ : ℝ) + 2 * ((t ^ 6 : ℕ) : ℝ) + 1 +
          8064 * (t : ℝ) ^ 7 * Real.log (t : ℝ) := by
      simpa only [← pow_mul, show (6 : ℕ) * 2 = 12 by norm_num] using
        hbound.trans (add_le_add_right hmain _)
    nlinarith [hboundary, hmainK]
  calc
    _ ≤ K * (t : ℝ) ^ 7 * (1 + Real.log (t : ℝ)) := hfinal
    _ = (t : ℝ) ^ 7 * (K * (1 + Real.log (t : ℝ))) := by ring
    _ ≤ (t : ℝ) ^ 7 * t := mul_le_mul_of_nonneg_left hs (pow_nonneg htp.le 7)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandPolynomialLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete positive-power lower bound at twelfth powers -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_polynomial_lower {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) :
    ∀ᶠ t : ℕ in atTop,
      (t : ℝ) ^ 3 ≤ ((summandPrefix A (t ^ 12)).card : ℝ) := by
  have htend : Tendsto (fun t : ℕ => t ^ 12) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    (constant_log_linear_small 48 (by norm_num))
  filter_upwards [h.symm.summand_polynomial_bootstrap hA,
    htend.eventually h.coverage_product_lower, hsmall,
    eventually_ge_atTop (2 : ℕ)] with t hu hl hs ht
  have htp : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hlog : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  let a : ℝ := (summandPrefix A (t ^ 12)).card
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hlogs : 4 * Real.log ((t ^ 12 : ℕ) : ℝ) ≤ t := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    change 48 * (1 + Real.log (t : ℝ)) ≤ (t : ℝ) at hs
    linarith
  have hlogp : 0 < 4 * Real.log ((t ^ 12 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    positivity
  have hp : (t : ℝ) ^ 12 ≤ a * (t : ℝ) ^ 8 * (4 * Real.log ((t ^ 12 : ℕ) : ℝ)) := by
    apply (div_le_iff₀ hlogp).mp
    simpa only [Nat.cast_pow] using hl.trans (mul_le_mul_of_nonneg_left hu ha)
  have hh : (t : ℝ) ^ 12 ≤ a * (t : ℝ) ^ 8 * t :=
    hp.trans (mul_le_mul_of_nonneg_left hlogs (mul_nonneg ha (pow_nonneg htp.le 8)))
  have hcancel : (t : ℝ) ^ 9 * (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 9 * a := by
    calc
      _ = (t : ℝ) ^ 12 := by ring
      _ ≤ _ := hh
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (pow_pos htp 9)).mp hcancel

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandSquareUpper
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-root upper bound at square endpoints -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_square_upper {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Infinite) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ q : ℕ in atTop,
      ((summandPrefix A (q ^ 2)).card : ℝ) ≤ C * q * Real.log (q : ℝ) ^ 2 := by
  obtain ⟨N₀, hcomp⟩ := h.summand_square_comparison hB.nonempty
  refine ⟨N₀ + 19203, by positivity, ?_⟩
  have htend : Tendsto (fun q : ℕ => q ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hloglarge := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hcomp, htend.eventually (h.symm.summand_polynomial_lower hB),
    hloglarge, eventually_ge_atTop (3 : ℕ)] with q hc hp hl hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  change 1 ≤ Real.log (q : ℝ) at hl
  have hp' : (q : ℝ) ^ 6 ≤ ((summandPrefix B (q ^ 24)).card : ℝ) := by
    simpa only [← pow_mul, Nat.cast_pow] using hp
  have h3q : 3 * (q : ℝ) ≤ (q : ℝ) ^ 6 := by
    have hq5 : (q : ℝ) ≤ (q : ℝ) ^ 5 := le_self_pow₀ hq1 (by norm_num)
    have h3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
    calc
      _ ≤ (q : ℝ) ^ 5 * q := mul_le_mul_of_nonneg_right (h3.trans hq5) hqp.le
      _ = _ := by ring
  have hbp : (0 : ℝ) < (summandPrefix B (q ^ 24)).card := (by positivity : 0 < (q : ℝ) ^ 6).trans_le hp'
  have hbne : (summandPrefix B (q ^ 24)).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast hbp)
  have hfrac : 3 * (q : ℝ) / ((summandPrefix B (q ^ 24)).card : ℝ) ≤ 1 :=
    (div_le_iff₀ hbp).mpr (by simpa using h3q.trans hp')
  have hlog2 : Real.log (2 * (q : ℝ)) ≤ 2 * Real.log (q : ℝ) := by
    rw [Real.log_mul (by norm_num) hqp.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ q by exact_mod_cast (by omega : 2 ≤ q))
    linarith
  have hlogY : Real.log ((q ^ 24 : ℕ) : ℝ) +
      3 * (q : ℝ) / ((summandPrefix B (q ^ 24)).card : ℝ) ≤ 25 * Real.log (q : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    linarith
  have hbound := hc (q ^ 24) (one_le_pow₀ (by omega : 1 ≤ q)) hbne
  have hmain : 384 * (q : ℝ) * Real.log (2 * (q : ℝ)) *
      (Real.log ((q ^ 24 : ℕ) : ℝ) +
        3 * (q : ℝ) / ((summandPrefix B (q ^ 24)).card : ℝ)) ≤
          19200 * q * Real.log (q : ℝ) ^ 2 := by
    calc
      _ ≤ 384 * (q : ℝ) * (2 * Real.log (q : ℝ)) * (25 * Real.log (q : ℝ)) := by
        gcongr
      _ = _ := by ring
  have hlogSq : 1 ≤ Real.log (q : ℝ) ^ 2 := by nlinarith
  have hboundary : (N₀ : ℝ) + 2 * q + 1 ≤
      (N₀ + 3 : ℝ) * q * Real.log (q : ℝ) ^ 2 := by
    calc
      _ ≤ (N₀ + 3 : ℝ) * q := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N₀) (sub_nonneg.mpr hq1)]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hlogSq
  have hh := hbound.trans (add_le_add_right hmain _)
  nlinarith [hboundary]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandSqrtUpper
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing the summand upper bound from squares to every cutoff -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_sqrt_upper {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Infinite) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ((summandPrefix A N).card : ℝ) ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 := by
  obtain ⟨C, hC, hupper⟩ := h.summand_square_upper hB
  have htend : Tendsto (fun N : ℕ => N.sqrt + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b ^ 2)] with N hN
    have hh := Nat.le_sqrt'.mpr hN
    omega
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [htend.eventually hupper, eventually_ge_atTop (2 : ℕ)] with N hu hN
  let q := N.sqrt + 1
  have hqp : (0 : ℝ) < q := by dsimp [q]; positivity
  have hqN : q ≤ N := by
    dsimp [q]
    have hh := Nat.sqrt_lt_self (by omega : 1 < N)
    omega
  have hNN : N ≤ q ^ 2 := (Nat.lt_succ_sqrt' N).le
  have hprefix : summandPrefix A N ⊆ summandPrefix A (q ^ 2) := by
    intro a ha
    obtain ⟨ha, han⟩ := mem_summandPrefix A N a |>.mp ha
    exact mem_summandPrefix A (q ^ 2) a |>.mpr ⟨ha, han.trans hNN⟩
  have hc : ((summandPrefix A N).card : ℝ) ≤ (summandPrefix A (q ^ 2)).card := by
    exact_mod_cast Finset.card_le_card hprefix
  have hroot : (q : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    have hh : (N.sqrt : ℝ) ≤ Real.sqrt (N : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' N)
    have hone : 1 ≤ Real.sqrt (N : ℝ) :=
      (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr (by exact_mod_cast (by omega : 1 ≤ N))
    dsimp [q]
    push_cast
    linarith
  have hlog : Real.log (q : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hqp (by exact_mod_cast hqN)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by dsimp [q]; norm_cast; omega)
  calc
    _ ≤ ((summandPrefix A (q ^ 2)).card : ℝ) := hc
    _ ≤ C * q * Real.log (q : ℝ) ^ 2 := hu
    _ ≤ C * (2 * Real.sqrt (N : ℝ)) * Real.log (N : ℝ) ^ 2 := by gcongr
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandSqrtLower
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime coverage gives the matching lower bound for each summand -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_sqrt_lower {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ ((summandPrefix A N).card : ℝ) := by
  obtain ⟨C, hC, hupper⟩ := h.symm.summand_sqrt_upper hA
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  filter_upwards [hupper, h.coverage_product_lower, eventually_ge_atTop (2 : ℕ)]
    with N hu hl hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNp
  let a : ℝ := (summandPrefix A N).card
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hh : (N : ℝ) ≤ a * (C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2) *
      (4 * Real.log (N : ℝ)) :=
    (div_le_iff₀ (by positivity : 0 < 4 * Real.log (N : ℝ))).mp
      (hl.trans (mul_le_mul_of_nonneg_left hu ha))
  have hc : Real.sqrt (N : ℝ) ≤ 4 * C * a * Real.log (N : ℝ) ^ 3 := by
    apply (mul_le_mul_iff_right₀ hroot).mp
    calc
      Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N := by nlinarith [Real.sq_sqrt hNp.le]
      _ ≤ _ := hh
      _ = Real.sqrt (N : ℝ) * (4 * C * a * Real.log (N : ℝ) ^ 3) := by ring
  change (1 / (4 * C)) * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ a
  apply (div_le_iff₀ (pow_pos hlog 3)).mpr
  rw [one_div, inv_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < 4 * C)).mpr
  nlinarith [hc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandSizeProof
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The required summand-size theorem, without a published-input hypothesis

The proof uses the proved additive sieve and actual prime distribution. The
finite fixed-shift sieve gives logarithmic growth, exponential sampling gives
a concrete polynomial bootstrap, and the two-cutoff collision estimate gives
the final square-root bounds. This supplies the exact consequence recorded
from Elsholtz (2006), Theorem 1.9.
-/

namespace Ostmann

open Filter

 theorem publishedSummandSizeBound_oai : PublishedSummandSizeBound := by
  intro A B hA hB h
  obtain ⟨aA, haA, hAl⟩ := h.summand_sqrt_lower hA
  obtain ⟨aB, haB, hBl⟩ := h.symm.summand_sqrt_lower hB
  obtain ⟨CA, hCA, hAu⟩ := h.summand_sqrt_upper hB
  obtain ⟨CB, hCB, hBu⟩ := h.symm.summand_sqrt_upper hA
  let a := min aA aB
  let C := max CA CB
  refine ⟨a, C, lt_min haA haB, lt_max_of_lt_left hCA, ?_⟩
  have hev : ∀ᶠ N : ℕ in atTop,
      a * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ (summandPrefix A N).card ∧
      (summandPrefix A N).card ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 ∧
      a * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ (summandPrefix B N).card ∧
      (summandPrefix B N).card ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 := by
    filter_upwards [hAl, hBl, hAu, hBu, eventually_ge_atTop (2 : ℕ)] with N hAl hBl hAu hBu hN
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply le_trans ?_ hAl
      dsimp [a]
      gcongr
      exact min_le_left _ _
    · apply le_trans hAu
      dsimp [C]
      gcongr
      exact le_max_left _ _
    · apply le_trans ?_ hBl
      dsimp [a]
      gcongr
      exact min_le_right _ _
    · apply le_trans hBu
      dsimp [C]
      gcongr
      exact le_max_right _ _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  exact ⟨N₀, fun N hN _ => hN₀ N hN⟩

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.publishedSummandSizeBound_oai := @OAI.Ostmann.publishedSummandSizeBound_oai
