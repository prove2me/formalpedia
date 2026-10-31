-- Prove2me | solution 1 for OAI.Ostmann.eventual_character_final_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:05:14.549718+00:00
-- url     : https://prove2.me/submissions/35336499-9ca1-43ec-91cf-a21a9764b071

import Mathlib
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_eventual_constituent_final_pair_decay
import Theorems.Thm_OAI_Ostmann_eventual_selected_final_natural_energy_comparison

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticErrorRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the fixed-depth arithmetic comparison costs

The polynomial and spectator costs in Section 8 are dominated by the
double-exponential savings. The strict numerical gaps in the manuscript
therefore survive the finite history and equality-pattern sums.
-/

namespace Ostmann

open Filter Asymptotics

theorem arithmetic_exponent_absorption (a b d C c : ℝ) (n : ℕ)
    (hb : 0 < b) (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      C * L ^ n + C * L * Real.exp (a * L) - c * Real.exp (b * L) ≤
        -Real.exp (d * L) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop n hb).const_mul_left C
  have hm : (fun L : ℝ => C * (Real.exp (a * L) * L)) =o[atTop]
      (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_one] using (isLittleO_exp_mul_rpow_of_lt 1 hab).const_mul_left C
  have he : (fun L : ℝ => Real.exp (d * L)) =o[atTop] (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_zero, mul_one] using isLittleO_exp_mul_rpow_of_lt 0 hdb
  have h := ((hp.add hm).add he).bound hc
  filter_upwards [h] with L hL
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hL
  have hle := (le_abs_self _).trans hL
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveGaussFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact primitive-character Fourier transform at composite modulus

This supplies the complete transform and Gauss normalization needed in the
quadratic Poisson step, using the proved library character identities.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem primitive_character_fourier {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (a : ZMod N) :
    additiveFourier χ a = (N : ℂ)⁻¹ * χ⁻¹ (-a) * gaussSum χ ZMod.stdAddChar := by
  rw [additiveFourier_apply]
  have heq : (∑ x : ZMod N, χ x * ZMod.stdAddChar (-(x * a))) =
      gaussSum χ ((ZMod.stdAddChar (N := N)).mulShift (-a)) := by
    simp only [gaussSum, AddChar.mulShift_apply]
    congr 1
    funext x
    rw [neg_mul, mul_comm a x]
  rw [heq, gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (-a)]
  ring

/-- Parseval gives the primitive Gauss-sum norm without a prime-modulus
restriction and without assuming a separate analytic input. -/
theorem primitive_gauss_norm_sq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ ^ 2 = (N : ℝ) := by
  let E : ℝ := ∑ a : ZMod N, ‖χ a‖ ^ 2
  have hE : 0 < E := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (ZMod N)))
      (f := fun a => ‖χ a‖ ^ 2) (fun a _ => sq_nonneg ‖χ a‖) (Finset.mem_univ (1 : ZMod N))
    have h1 : (1 : ℝ) ≤ E := by simpa [E] using hh
    linarith
  have hinv : (∑ a : ZMod N, ‖χ⁻¹ (-a)‖ ^ 2) = E := by
    simp_rw [← MulChar.star_apply', norm_star]
    exact (Equiv.neg (ZMod N)).bijective.sum_comp (fun a => ‖χ a‖ ^ 2)
  have hfourier : (∑ a : ZMod N, ‖additiveFourier χ a‖ ^ 2) =
      (N : ℝ)⁻¹ ^ 2 * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * E := by
    rw [← hinv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [primitive_character_fourier χ hχ a]
    simp only [Complex.norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    ring
  have heq := additiveFourier_energy χ
  rw [hfourier] at heq
  change E = (N : ℝ) * ((N : ℝ)⁻¹ ^ 2 * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 * E) at heq
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  apply mul_right_cancel₀ hE.ne'
  field_simp [hN] at heq
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TupleCharacterPoisson
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Poisson summation and the initial graph phase of a character tuple -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap ComplexConjugate Classical

theorem primitiveGaussPhase_norm {p : ℕ} [NeZero p]
    (χ : DirichletCharacter ℂ p) (hχ : χ.IsPrimitive) :
    ‖primitiveGaussPhase χ‖ = 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hg := primitive_gauss_norm_sq χ hχ
  have he : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (p : ℝ) := by
    nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (p : ℝ),
      norm_nonneg (gaussSum χ ZMod.stdAddChar)]
  rw [primitiveGaussPhase, norm_div, he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hp).ne']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorPairCode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor codes from the actual graph update -/

namespace Ostmann

theorem transferCopySign_sq (t : Bool) : transferCopySign t ^ 2 = 1 := by
  cases t <;> rfl

/-- Normalize by the new bulk parity. Its inverse equals itself, since it is
a sign. Both entries come directly from the copied graph, including the
cross-copy incoming-pivot coefficient. -/
theorem transferred_anchor_pair {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (a i : H) (α ε : ℤ)
    (hε : ε = 1 ∨ ε = -1)
    (hincoming : b (some (.inl a)) (some (.inl i)) = ε)
    (hpivot : b (some (.inl a)) none = α) (t : Bool) :
    (transferCopySign t * ε * transferredGraph b (.inl (true, a)) (.inl (t, i)),
      transferCopySign t * ε * transferredGraph b (.inl (false, a)) (.inl (t, i))) =
      anchorSignPair α ε t := by
  rcases hε with rfl | rfl <;> cases t <;>
    simp [anchorSignPair, transferredGraph, transferCopySign, hincoming, hpivot]

theorem anchorSignPair_determines_parity (α ε ε' : ℤ) (t t' : Bool)
    (hα : α = 1 ∨ α = -1)
    (h : anchorSignPair α ε t = anchorSignPair α ε' t') : ε = ε' := by
  rcases hα with rfl | rfl <;> cases t <;> cases t' <;>
    simp only [anchorSignPair, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      Prod.mk.injEq, neg_one_mul, neg_neg, one_mul] at h <;> omega

theorem finiteAnchorCode_prefix_parity {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) (t t' : Fin n → Bool)
    (hcode : finiteAnchorCode α t = finiteAnchorCode α t') (j : Fin n) :
    copyPathParity (finiteCopyPath t) j = copyPathParity (finiteCopyPath t') j := by
  exact anchorSignPair_determines_parity _ _ _ _ _ (hα j) (congrFun hcode j)

/-- All code pairs determine the incoming parities; the final parity then
determines the last copy sign as well. -/
theorem finiteAnchorCode_final_injective {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) :
    Function.Injective (fun t : Fin n → Bool => (finiteAnchorCode α t, finalCopyParity t)) := by
  intro t t' he
  have hcode := congrArg Prod.fst he
  have hfinal := congrArg Prod.snd he
  funext j
  have hbefore := finiteAnchorCode_prefix_parity α hα t t' hcode j
  have hafter : copyPathParity (finiteCopyPath t) (j.val + 1) =
      copyPathParity (finiteCopyPath t') (j.val + 1) := by
    by_cases hj : j.val + 1 < n
    · exact finiteAnchorCode_prefix_parity α hα t t' hcode ⟨j.val + 1, hj⟩
    · have hjn : j.val + 1 = n := by omega
      simpa only [hjn, finalCopyParity] using hfinal
  simp only [copyPathParity, finiteCopyPath, j.isLt, dite_true, Fin.eta] at hafter
  rw [hbefore] at hafter
  apply transferCopySign_injective
  exact mul_right_cancel₀ (by rcases copyPathParity_sign (finiteCopyPath t') j with h | h <;> omega) hafter

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorOneSidedEdge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A changed anchor code supplies a one-sided squared character -/

namespace Ostmann

theorem changed_anchor_code_one_sided (ε ε' c c' : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1)
    (hc : c = 1 ∨ c = -1) (hc' : c' = 1 ∨ c' = -1) (hne : c ≠ c') :
    ((ε * c - ε' * c' = 2 ∨ ε * c - ε' * c' = -2) ∧ ε - ε' = 0) ∨
      (ε * c - ε' * c' = 0 ∧ (ε - ε' = 2 ∨ ε - ε' = -2)) := by
  rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;> norm_num at *

theorem signed_square_nonprincipal {p : ℕ} (χ : DirichletCharacter ℂ p)
    (hχ : χ ^ 2 ≠ 1) (e : ℤ) (he : e = 2 ∨ e = -2) : χ ^ e ≠ 1 := by
  rcases he with rfl | rfl
  · simpa only [zpow_ofNat] using hχ
  · intro h
    have hinv := congrArg Inv.inv h
    simp only [zpow_neg, inv_inv, inv_one, zpow_ofNat] at hinv
    exact hχ hinv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalParityPaths
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two equally sized final-parity classes of actual copy paths -/

namespace Ostmann

open scoped Classical

theorem card_parityPaths (n : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    Fintype.card (ParityPaths n ε) = 2 ^ n := by
  classical
  rw [Fintype.card_congr (parityPathsEquiv n ε hε)]
  simp

theorem card_finalParityReassignments (n m : ℕ) :
    Fintype.card (FinalParityReassignments n m) = ((Nat.factorial (2 ^ n)) ^ 2) ^ m := by
  classical
  simp only [FinalParityReassignments, Fintype.card_fun, Fintype.card_prod, Fintype.card_perm,
    card_parityPaths n 1 (Or.inl rfl), card_parityPaths n (-1) (Or.inr rfl), Fintype.card_fin]
  rw [pow_two]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalReassignments
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual independent, parity-preserving bulk reassignments -/

namespace Ostmann

open scoped Classical

theorem paritySlotPerm_preserves_parity {n m : ℕ} (e : FinalParityReassignments n m)
    (x : ParityPathSum n × Fin m) :
    finalCopyParity (parityPathValue (paritySlotPerm e x).1) = finalCopyParity (parityPathValue x.1) := by
  rcases x with ⟨t, i⟩
  cases t with
  | inl t => exact ((e i).1 t).property.trans t.property.symm
  | inr t => exact ((e i).2 t).property.trans t.property.symm

theorem paritySlotPerm_preserves_position {n m : ℕ} (e : FinalParityReassignments n m)
    (x : ParityPathSum n × Fin m) : (paritySlotPerm e x).2 = x.2 := rfl

theorem paritySlotPerm_injective {n m : ℕ} :
    Function.Injective (@paritySlotPerm n m) := by
  intro e f hef
  funext i
  apply Prod.ext
  · apply Equiv.ext
    intro t
    have h := congrArg (fun g => (g (.inl t, i)).1) hef
    exact Sum.inl.inj h
  · apply Equiv.ext
    intro t
    have h := congrArg (fun g => (g (.inr t, i)).1) hef
    exact Sum.inr.inj h

/-- Distinct members of the constructed reassignment family move some prime
to a path with a different anchor code, while retaining its final parity. -/
theorem distinct_reassignments_change_code {n m : ℕ}
    (α : Fin (n + 1) → ℤ) (hα : ∀ j, α j = 1 ∨ α j = -1)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ x : ParityPathSum n × Fin m,
      finiteAnchorCode α (parityPathValue (paritySlotPerm e x).1) ≠
        finiteAnchorCode α (parityPathValue (paritySlotPerm f x).1) := by
  by_contra h
  push Not at h
  apply hef
  apply paritySlotPerm_injective
  apply Equiv.ext
  intro x
  apply Prod.ext
  · apply parityPathValue_injective n
    apply finiteAnchorCode_final_injective α hα
    apply Prod.ext
    · exact h x
    · exact (paritySlotPerm_preserves_parity e x).trans (paritySlotPerm_preserves_parity f x).symm
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalReassignmentInteraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting the actual small-anchor interaction between two reassignments -/

namespace Ostmann

theorem anchorCodeEntry_sign {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) (t : Fin n → Bool) (j : Fin n) (b : Bool) :
    anchorCodeEntry α t j b = 1 ∨ anchorCodeEntry α t j b = -1 := by
  have hp := copyPathParity_sign (finiteCopyPath t) j
  rcases hα j with ha | ha <;> rcases hp with hp | hp <;>
    cases hb : t j <;> cases b <;>
    simp [anchorCodeEntry, finiteAnchorCode, anchorSignPair, ha, hp, hb]

theorem distinct_anchor_code_entry {n : ℕ} (α : Fin n → ℤ) (t u : Fin n → Bool)
    (hne : finiteAnchorCode α t ≠ finiteAnchorCode α u) :
    ∃ j b, anchorCodeEntry α t j b ≠ anchorCodeEntry α u j b := by
  by_contra h
  push Not at h
  apply hne
  funext j
  apply Prod.ext
  · exact h j true
  · exact h j false

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorGraphEvolution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The anchor coefficients through their actual creation and later copies -/

namespace Ostmann

theorem copyPathParity_snoc_prefix {n : ℕ} (t : Fin n → Bool) (b : Bool)
    (j : ℕ) (hj : j ≤ n) :
    copyPathParity (finiteCopyPath (Fin.snoc t b)) j = copyPathParity (finiteCopyPath t) j := by
  apply copyPathParity_congr_prefix
  intro h hh
  have hhn : h < n := lt_of_lt_of_le hh hj
  simp only [finiteCopyPath, hhn, Nat.lt_succ_of_lt hhn, dite_true]
  exact @Fin.snoc_castSucc n (fun _ => Bool) b t ⟨h, hhn⟩

theorem anchorCodeEntry_snoc {n : ℕ} (α : Fin (n + 1) → ℤ)
    (t : Fin n → Bool) (u b : Bool) (j : Fin n) :
    anchorCodeEntry α (Fin.snoc t u) j.castSucc b =
      anchorCodeEntry (fun j => α j.castSucc) t j b := by
  have hp := copyPathParity_snoc_prefix t u j (Nat.le_of_lt j.isLt)
  simp only [anchorCodeEntry, finiteAnchorCode, Fin.val_castSucc, hp,
    @Fin.snoc_castSucc n (fun _ => Bool) u t j]

/-- This is exactly the outside-anchor row of `transferredGraph`: every
later copy multiplies its incoming coefficient by that copy's sign. -/
theorem anchorIncoming_snoc_old {n : ℕ} (α : Fin (n + 1) → ℤ)
    (t : Fin n → Bool) (u b : Bool) (j : Fin n) :
    anchorIncoming α (Fin.snoc t u) j.castSucc b =
      transferCopySign u * anchorIncoming (fun j => α j.castSucc) t j b := by
  unfold anchorIncoming
  rw [finalCopyParity_snoc, anchorCodeEntry_snoc, mul_assoc]

theorem anchorIncoming_snoc_new {n : ℕ} (α : Fin (n + 1) → ℤ)
    (t : Fin n → Bool) (u b : Bool) :
    anchorIncoming α (Fin.snoc t u) (Fin.last n) b =
      (transferCopySign u * finalCopyParity t) *
        (if b then (anchorSignPair (α (Fin.last n)) (finalCopyParity t) u).1
         else (anchorSignPair (α (Fin.last n)) (finalCopyParity t) u).2) := by
  have hp := copyPathParity_snoc_prefix t u n le_rfl
  unfold anchorIncoming
  rw [finalCopyParity_snoc]
  congr 1
  simp only [anchorCodeEntry, finiteAnchorCode, Fin.val_last, hp,
    @Fin.snoc_last n (fun _ => Bool) u t]
  rfl

/-- At its reserved step the unnormalized coefficient is precisely the
edge created by the graph transfer, for either clone of the fresh anchor. -/
theorem anchorIncoming_created_by_transfer {H Y : Type*}
    (graph : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (a i : H)
    {n : ℕ} (α : Fin (n + 1) → ℤ) (t : Fin n → Bool) (u b : Bool)
    (hincoming : graph (some (.inl a)) (some (.inl i)) = finalCopyParity t)
    (hpivot : graph (some (.inl a)) none = α (Fin.last n)) :
    anchorIncoming α (Fin.snoc t u) (Fin.last n) b =
      transferredGraph graph (.inl (b, a)) (.inl (u, i)) := by
  have hs := copyPathParity_sign (finiteCopyPath t) n
  change finalCopyParity t = 1 ∨ finalCopyParity t = -1 at hs
  have hpair := transferred_anchor_pair graph a i (α (Fin.last n)) (finalCopyParity t)
    hs hincoming hpivot u
  rw [anchorIncoming_snoc_new]
  have hsq : (transferCopySign u * finalCopyParity t) ^ 2 = 1 := by
    rw [mul_pow, transferCopySign_sq]
    rcases hs with hs | hs <;> simp only [hs] <;> norm_num
  cases b
  · have he := congrArg Prod.snd hpair
    dsimp only at he
    simp only [Bool.false_eq_true, ite_false, if_false]
    rw [← he]
    rw [← mul_assoc, ← pow_two, hsq, one_mul]
  · have he := congrArg Prod.fst hpair
    dsimp only at he
    simp only [ite_true, if_true]
    rw [← he]
    rw [← mul_assoc, ← pow_two, hsq, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GraphCopySchedule
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph on the literal copied and retained slot labels

The ambient label type includes both alternatives at a transfer. The actual
partition restricts the copied alternative to H and the retained alternative to
Y. Thus copying and retaining never identify two surviving slots. -/

namespace Ostmann

universe u

/-- Incoming edges from an unused reserved anchor simply accumulate the signs
of the copied word. The pivot sequence does not enter this identity. -/
theorem copyScheduleGraph_fresh_to_path {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (a i : I) (t : Fin n → Bool) :
    copyScheduleGraph g pivot n (copyScheduleOutside n a) (copySchedulePath n t i) =
      finalCopyParity t * g a i := by
  induction n with
  | zero => simp [copyScheduleGraph, copyScheduleOutside, copySchedulePath, finalCopyParity, copyPathParity]
  | succ n ih =>
    change transferCopySign (t (Fin.last n)) *
      copyScheduleGraph g pivot n (copyScheduleOutside n a)
        (copySchedulePath n (fun j => t j.castSucc) i) = _
    rw [ih]
    have ht : Fin.snoc (fun j => t j.castSucc) (t (Fin.last n)) = t := by
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    rw [← ht, finalCopyParity_snoc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_assoc]

theorem copyScheduleGraph_fresh_to_positive {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (a i : I) :
    copyScheduleGraph g pivot n (copyScheduleOutside n a) (copySchedulePositive n i) = g a i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change transferCopySign true *
      copyScheduleGraph g pivot n (copyScheduleOutside n a) (copySchedulePositive n i) = _
    simpa [transferCopySign] using ih

/-- A regular original word has the same signed edge to every future active
pivot. The hypothesis refers only to the initial graph's off-diagonal edges. -/
theorem copyScheduleGraph_path_to_positive {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (hp : ∀ k < n, g i (pivot k) = 1) (ha : g i a = 1) (t : Fin n → Bool) :
    copyScheduleGraph g pivot n (copySchedulePath n t i) (copySchedulePositive n a) =
      finalCopyParity t := by
  induction n generalizing a with
  | zero => simpa [copyScheduleGraph, copySchedulePath, copySchedulePositive, finalCopyParity, copyPathParity] using ha
  | succ n ih =>
    change (if t (Fin.last n) = true then
      transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copySchedulePath n (fun j => t j.castSucc) i) (copySchedulePositive n a)
      else transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copySchedulePath n (fun j => t j.castSucc) i) (copySchedulePositive n (pivot n))) = _
    have hprev : ∀ k < n, g i (pivot k) = 1 := fun k hk => hp k (by omega)
    rw [ih a hprev ha, ih (pivot n) hprev (hp n (by omega))]
    split_ifs <;>
      have ht : Fin.snoc (fun j => t j.castSucc) (t (Fin.last n)) = t := by
        ext j
        refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    all_goals rw [← ht, finalCopyParity_snoc]; simp

/-- The same regular row holds against every anchor not yet used. -/
theorem copyScheduleGraph_path_to_fresh {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (ha : g i a = 1) (t : Fin n → Bool) :
    copyScheduleGraph g pivot n (copySchedulePath n t i) (copyScheduleOutside n a) =
      finalCopyParity t := by
  induction n with
  | zero => simpa [copyScheduleGraph, copySchedulePath, copyScheduleOutside, finalCopyParity, copyPathParity] using ha
  | succ n ih =>
    change transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
      (copySchedulePath n (fun j => t j.castSucc) i) (copyScheduleOutside n a) = _
    rw [ih]
    have ht : Fin.snoc (fun j => t j.castSucc) (t (Fin.last n)) = t := by
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    rw [← ht, finalCopyParity_snoc]
    simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAnchorGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.copyScheduleVertexFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor codes derived from the full copied-slot schedule -/

namespace Ostmann

open scoped Classical

/-- Every outgoing word-to-anchor edge is its final copy parity. -/
theorem copyScheduleGraph_path_to_anchor {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (hp : ∀ k < n, g i (pivot k) = 1) (ha : g i a = 1)
    (t : Fin n → Bool) (j : ℕ) (hj : j < n) (b : Bool) :
    copyScheduleGraph g pivot n (copySchedulePath n t i) (copyScheduleAnchor n j b a) =
      finalCopyParity t := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hprev : ∀ k < n, g i (pivot k) = 1 := fun k hk => hp k (by omega)
    have ht : Fin.snoc (fun k => t k.castSucc) (t (Fin.last n)) = t :=
      Fin.snoc_init_self t
    by_cases hjn : j = n
    · subst j
      have hanc : copyScheduleAnchor (n + 1) n b a =
          Sum.inl (b, copyScheduleOutside n a) := copyScheduleAnchor_new n b a
      rw [hanc]
      change (if t (Fin.last n) = b then
        transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
          (copySchedulePath n (fun k => t k.castSucc) i) (copyScheduleOutside n a)
        else transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
          (copySchedulePath n (fun k => t k.castSucc) i) (copySchedulePositive n (pivot n))) = _
      rw [copyScheduleGraph_path_to_fresh g pivot n i a ha,
        copyScheduleGraph_path_to_positive g pivot n i (pivot n) hprev (hp n (by omega))]
      rw [← ht, finalCopyParity_snoc]
      simp
    · have hj' : j < n := by omega
      have hanc : copyScheduleAnchor (n + 1) j b a =
          Sum.inr (copyScheduleAnchor n j b a) := copyScheduleAnchor_old n _ b a hjn
      rw [hanc]
      change transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copySchedulePath n (fun k => t k.castSucc) i) (copyScheduleAnchor n j b a) = _
      rw [ih hprev (fun k => t k.castSucc) hj']
      rw [← ht, finalCopyParity_snoc]
      simp

/-- The incoming anchor edge has exactly the previously constructed code.
The initial graph is the only source of the two hypotheses. -/
theorem copyScheduleGraph_anchor_to_path {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i a : I)
    (hp : ∀ k < n, g a (pivot k) = 1) (ha : g a i = 1)
    (t : Fin n → Bool) (j : Fin n) (b : Bool) :
    copyScheduleGraph g pivot n (copyScheduleAnchor n j b a) (copySchedulePath n t i) =
      anchorIncoming (fun _ => 1) t j b := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    have ht : Fin.snoc (fun k => t k.castSucc) (t (Fin.last n)) = t :=
      Fin.snoc_init_self t
    have hprev : ∀ k < n, g a (pivot k) = 1 := fun k hk => hp k (by omega)
    by_cases hjn : j.val = n
    · have hjlast : j = Fin.last n := Fin.ext hjn
      subst j
      let G := fun x y => copyScheduleGraph g pivot n
        (copySchedulePredecessor (copySchedulePositive n (pivot n)) x)
        (copySchedulePredecessor (copySchedulePositive n (pivot n)) y)
      have hinc : G (some (.inl (copyScheduleOutside n a)))
          (some (.inl (copySchedulePath n (fun k => t k.castSucc) i))) =
            finalCopyParity (fun k => t k.castSucc) := by
        change copyScheduleGraph g pivot n (copyScheduleOutside n a)
          (copySchedulePath n (fun k => t k.castSucc) i) = _
        rw [copyScheduleGraph_fresh_to_path, ha, mul_one]
      have hpiv : G (some (.inl (copyScheduleOutside n a))) none = 1 := by
        change copyScheduleGraph g pivot n (copyScheduleOutside n a)
          (copySchedulePositive n (pivot n)) = _
        rw [copyScheduleGraph_fresh_to_positive, hp n (by omega)]
      have hc := anchorIncoming_created_by_transfer G (copyScheduleOutside n a)
        (copySchedulePath n (fun k => t k.castSucc) i)
        (α := fun _ => 1) (fun k => t k.castSucc) (t (Fin.last n)) b hinc hpiv
      have he : copyScheduleGraph g pivot (n + 1)
          (Sum.inl (b, copyScheduleOutside n a))
          (Sum.inl (t (Fin.last n), copySchedulePath n (fun k => t k.castSucc) i)) =
            anchorIncoming (fun _ => 1) (Fin.snoc (fun k => t k.castSucc) (t (Fin.last n)))
              (Fin.last n) b := hc.symm
      rw [ht] at he
      have hanc : copyScheduleAnchor (n + 1) n b a =
          Sum.inl (b, copyScheduleOutside n a) := copyScheduleAnchor_new n b a
      rw [show (Fin.last n).val = n from rfl, hanc]
      exact he
    · let j' : Fin n := ⟨j.val, by omega⟩
      have hjcast : j'.castSucc = j := Fin.ext rfl
      have hanc : copyScheduleAnchor (n + 1) j b a =
          Sum.inr (copyScheduleAnchor n j b a) := copyScheduleAnchor_old n _ b a hjn
      rw [hanc]
      change transferCopySign (t (Fin.last n)) * copyScheduleGraph g pivot n
        (copyScheduleAnchor n j b a) (copySchedulePath n (fun k => t k.castSucc) i) = _
      rw [ih hprev (fun k => t k.castSucc) j']
      rw [← ht, ← hjcast, anchorIncoming_snoc_old]
      simp

theorem initialCompleteGraph_of_ne {I : Type*} {i j : I} (h : i ≠ j) :
    initialCompleteGraph i j = 1 := by simp [initialCompleteGraph, h]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CommonHistoryPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonzero common modulus constructed from the actual small frequencies -/

namespace Ostmann

theorem historyFrequencyPeriod_le (frequencies : List ℤ) (V degree : ℕ)
    (hV : ∀ s ∈ frequencies, s.natAbs ≤ V) :
    historyFrequencyPeriod frequencies degree ≤ V ^ (frequencies.length * degree) := by
  have hb : historyFrequencyBase frequencies ≤ V ^ frequencies.length := by
    induction frequencies with
    | nil => simp [historyFrequencyBase]
    | cons s rest ih =>
      simp only [historyFrequencyBase, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      exact (Nat.mul_le_mul (hV s (by simp))
        (ih (fun t ht => hV t (by simp [ht])))).trans_eq (Nat.mul_comm _ _)
  exact (Nat.pow_le_pow_left hb degree).trans_eq (pow_mul V frequencies.length degree).symm

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete transfer system of word products and reconstructed pivots -/

namespace Ostmann

open scoped Classical

universe u

theorem ValidTransferHistory.nonzero_internal {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (ht : ValidTransferHistory sys n σ t) :
    NonzeroInternalFrequencies n t := by
  induction n generalizing σ with
  | zero => trivial
  | succ n ih =>
    obtain ⟨P, hp, hl, hr⟩ := ht
    exact ⟨hp.root_ne_zero, ih _ _ hl, ih _ _ hr⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferPeriods
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common residue period derived from the actual branching frequencies -/

namespace Ostmann

open scoped Classical

theorem internalFrequencyList_length (n : ℕ) (t : FrequencyTree ℤ n) :
    (internalFrequencyList n t).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [internalFrequencyList, List.length_cons, List.length_append, ih, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFullPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full small-frequency modulus, including every node's unit tests -/

namespace Ostmann

open scoped Classical

theorem internalFrequencyList_subset_all (n : ℕ) (t : FrequencyTree ℤ n) :
    ∀ s ∈ internalFrequencyList n t, s ∈ allFrequencyList n t := by
  induction n with
  | zero => simp [internalFrequencyList]
  | succ n ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact List.mem_cons_self ..
    · rcases List.mem_append.mp hs with hs | hs
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih _ s hs))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih _ s hs))

theorem allFrequencyList_length (n : ℕ) (t : FrequencyTree ℤ n) :
    (allFrequencyList n t).length = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allFrequencyList, List.length_cons, List.length_append, ih, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem wordTransferFullPeriod_le (n : ℕ) (t : FrequencyTree ℤ n) (B V : ℕ)
    (hV : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) :
    wordTransferFullPeriod n t B ≤
      V ^ ((2 ^ n - 1) * (B ^ (n + 1) + 1) + (2 ^ (n + 1) - 1)) := by
  have hi := historyFrequencyPeriod_le (internalFrequencyList n t) V (B ^ (n + 1) + 1)
    (fun s hs => hV s (internalFrequencyList_subset_all n t s hs))
  have ha := historyFrequencyPeriod_le (allFrequencyList n t) V 1 hV
  simp only [historyFrequencyPeriod, pow_one, mul_one] at ha
  rw [internalFrequencyList_length] at hi
  rw [allFrequencyList_length] at ha
  exact (Nat.mul_le_mul hi ha).trans_eq (pow_add _ _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledTemplateBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word-size bounds for the constructed copied-atom template -/

namespace Ostmann

open scoped Classical

theorem copyScheduleVertex_card {I : Type*} [Fintype I] (n : ℕ) :
    Fintype.card (CopyScheduleVertex I n) = 3 ^ n * Fintype.card I := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    exact Fintype.card_congr (Equiv.refl I)
  | succ n ih =>
    change Fintype.card ((Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n) = _
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    ring

theorem copyScheduleAtoms_zero_card {I : Type*} [Fintype I] (role : I → CopyScheduleRole) :
    Fintype.card (CopyScheduleAtoms role 0) = Fintype.card I := by
  let e : CopyScheduleAtoms role 0 ≃ I :=
    ⟨Subtype.val, fun i => ⟨i, True.intro⟩, (by intro i; rfl), (by intro i; rfl)⟩
  exact Fintype.card_congr e

theorem copyScheduleH_card_le {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleH role n) ≤ 3 ^ n * Fintype.card I := by
  rw [← copyScheduleVertex_card n]
  exact Fintype.card_subtype_le _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduledTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The atom schedule expanded into its actual prime constituents -/

namespace Ostmann

open scoped BigOperators Classical

theorem list_flatMap_length_bound {α β : Type*} (l : List α) (f : α → List β) (M : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ M) : (l.flatMap f).length ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    nlinarith

theorem reverseCopyLabelMap_list_length {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → List σ)
    (M : ℕ) (hM : 1 ≤ M) (hc : ∀ i, (current i).length ≤ M) :
    ∀ i, (reverseCopyLabelMap role n b [pivot] current i).length ≤ M := by
  intro i
  unfold reverseCopyLabelMap
  split_ifs
  · exact hc _
  · exact hM
  · exact hc _

theorem expandedHWord_length {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → List σ)
    (M : ℕ) (hc : ∀ i, (current i).length ≤ M) :
    (expandedHWord role n b current).length ≤ Fintype.card (CopyScheduleH role n) * M := by
  simpa only [expandedHWord, Finset.length_toList, Finset.card_univ] using
    list_flatMap_length_bound (Finset.univ.toList : List (CopyScheduleH role n))
      (fun i => current ⟨.inl (b, i.val), i.property⟩) M (fun _ _ => hc _)

theorem expandedScheduledTemplate_words_bounded {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ) (childBound pivotBound : ℕ → ℕ)
    (n M B : ℕ) (hM : 1 ≤ M) (hbase : Fintype.card (CopyScheduleAtoms role 0) * M + 1 ≤ B)
    (hH : ∀ j < n, 2 * Fintype.card (CopyScheduleH role j) * M + 4 ≤ B)
    (path : List Bool) (current : CopyScheduleAtoms role n → List σ)
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedScheduledTemplate role address childBound pivotBound n path current).WordsBounded B := by
  induction n generalizing path with
  | zero =>
    change (List.flatMap current (Finset.univ.toList : List (CopyScheduleAtoms role 0))).length + 1 ≤ B
    have hh := list_flatMap_length_bound (Finset.univ.toList : List (CopyScheduleAtoms role 0)) current M
      (fun i _ => hc i)
    simp only [Finset.length_toList, Finset.card_univ] at hh
    omega
  | succ n ih =>
    change _ ∧ _ ∧ _
    refine ⟨?_, ih (fun j hj => hH j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n true _ current M hM hc),
      ih (fun j hj => hH j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n false _ current M hM hc)⟩
    have hL := expandedHWord_length role n true current M hc
    have hR := expandedHWord_length role n false current M hc
    have hh := hH n (by omega)
    dsimp only
    nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact constituent words of the surviving grouped atoms -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduleConstituentWord_length {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) :
    (scheduleConstituentWord role size n v).length = size (copyScheduleOrigin n v.val) := by
  exact List.length_ofFn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fresh finite pivot coordinates for expanded prime-word templates -/

namespace Ostmann

open scoped Classical

/-- The prime-expanded template has a concrete polynomial word bound. -/
theorem expandedRootTemplate_size {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth : ℕ) (words : CopyScheduleAtoms role depth → List α)
    (childBound pivotBound : ℕ → ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hwords : ∀ i, (words i).length ≤ M) :
    (expandedRootTemplate role depth words childBound pivotBound).WordsBounded
      (2 * 3 ^ depth * Fintype.card I * M + 4) := by
  apply expandedScheduledTemplate_words_bounded role _ _ _ depth M _ hM
  · rw [copyScheduleAtoms_zero_card]
    have hp : 1 ≤ 3 ^ depth := Nat.one_le_pow _ _ (by omega)
    have hm := Nat.mul_le_mul_right (Fintype.card I * M) hp
    nlinarith only [hm]
  · intro j hj
    have hc := copyScheduleH_card_le role j
    have hp : 3 ^ j ≤ 3 ^ depth := Nat.pow_le_pow_right (by omega) (by omega)
    have hmul := Nat.mul_le_mul_right (Fintype.card I) hp
    have hmulM := Nat.mul_le_mul_right M (hc.trans hmul)
    nlinarith
  · intro i
    simpa only [List.length_map] using hwords i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicPrimeRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete dyadic covers of the prime ranges used by the prior comparison -/

namespace Ostmann

/-- A lower endpoint at least twice the modulus ensures every dyadic
interval in the cover is long enough for the uniform residue bound. -/
theorem dyadic_prime_range_cover (A B q : ℕ) (hq : 0 < q) (hA : 2 * q ≤ A)
    (S : Finset ℕ) (hS : ∀ p ∈ S, A ≤ p ∧ p ≤ B) :
    q ≤ 2 ^ Nat.log 2 A ∧
      ∀ p ∈ S, 2 ^ Nat.log 2 A ≤ p ∧ p < 2 ^ (Nat.log 2 A + (Nat.log 2 B + 1)) := by
  have hA0 : A ≠ 0 := by omega
  have hbound := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) A
  have hqpow : q ≤ 2 ^ Nat.log 2 A := by
    rw [pow_succ] at hbound
    omega
  refine ⟨hqpow, fun p hp => ⟨(Nat.pow_log_le_self 2 hA0).trans (hS p hp).1, ?_⟩⟩
  have hB := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) B
  apply ((hS p hp).2.trans_lt hB).trans_le
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Even a doubly exponential prime endpoint needs only exponentially
many dyadic blocks. The constant is explicit and independent of the tree. -/
theorem dyadic_prime_range_count (B : ℕ) (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hB : (B : ℝ) ≤ Real.exp (Real.exp (C * L))) :
    ((Nat.log 2 B + 1 : ℕ) : ℝ) ≤
      Real.exp ((C + Real.log ((Real.log 2)⁻¹ + 1)) * L) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : Real.log B ≤ Real.exp (C * L) := by
    by_cases hB0 : B = 0
    · subst B
      simp only [Nat.cast_zero, Real.log_zero]
      exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hB0)).mpr hB
  have hnat : (Nat.log 2 B : ℝ) ≤ Real.log B / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb B 2
  have hexp1 : 1 ≤ Real.exp (C * L) := Real.one_le_exp (mul_nonneg hC (by linarith))
  have hconstant : 1 ≤ (Real.log 2)⁻¹ + 1 := by linarith [inv_pos.mpr hlog2]
  have hconstantpos : 0 < (Real.log 2)⁻¹ + 1 := lt_of_lt_of_le (by norm_num) hconstant
  have hlogconst : 0 ≤ Real.log ((Real.log 2)⁻¹ + 1) := Real.log_nonneg hconstant
  calc
    _ ≤ Real.log B / Real.log 2 + 1 := by push_cast; linarith
    _ ≤ Real.exp (C * L) / Real.log 2 + 1 := by gcongr
    _ ≤ ((Real.log 2)⁻¹ + 1) * Real.exp (C * L) := by
      rw [div_eq_mul_inv]
      nlinarith
    _ = Real.exp (Real.log ((Real.log 2)⁻¹ + 1) + C * L) := by
      rw [Real.exp_add, Real.exp_log hconstantpos]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AtomTopSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top atom support as explicit original-prime tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem atomPairChecks_length {I V : Type*} [Fintype I]
    (words : I → List V) (M : ℕ) (hw : ∀ i, (words i).length ≤ M) :
    (atomPairChecks words).length ≤ (Fintype.card I * M) ^ 2 := by
  have hp (i j : I) :
      (if i = j then [] else (words i).flatMap fun v =>
        (words j).map (TopPrimeCondition.distinct v)).length ≤ M * M := by
    split_ifs
    · simp only [List.length_nil]; omega
    · apply (list_flatMap_length_bound (words i) _ M
        (fun _ _ => by simpa only [List.length_map] using hw j)).trans
      exact Nat.mul_le_mul_right M (hw i)
  have hi (i : I) :
      (Finset.univ.toList.flatMap fun j => if i = j then [] else
        (words i).flatMap fun v => (words j).map (TopPrimeCondition.distinct v)).length ≤
          Fintype.card I * (M * M) := by
    simpa only [Finset.length_toList, Finset.card_univ] using
      list_flatMap_length_bound Finset.univ.toList _ (M * M) (fun j _ => hp i j)
  calc
    _ ≤ Fintype.card I * (Fintype.card I * (M * M)) := by
      simpa only [atomPairChecks, Finset.length_toList, Finset.card_univ] using
        list_flatMap_length_bound Finset.univ.toList _ (Fintype.card I * (M * M)) (fun i _ => hi i)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedOutsideWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original prime constituents of each retained Y atom -/

namespace Ostmann

open scoped Classical

theorem expandedOriginalWord_length {V : Type*} {depth : ℕ}
    (w : List (ExpandedScheduledVariable V depth)) :
    (expandedOriginalWord w).length ≤ w.length := by
  induction w with
  | nil => rfl
  | cons v w ih => cases v <;> simp only [expandedOriginalWord, List.length_cons] <;> omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRangeBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete complexity of all replayed intermediate range tests -/

namespace Ostmann

open scoped Classical

theorem WordRangeDecoration.count_le {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (K : ℕ) (hD : D.CountBounded K) :
    D.count ≤ K * (2 ^ (n + 1) - 1) := by
  induction D with
  | leaf ranges => simpa only [count, CountBounded, Nat.zero_add, pow_one, Nat.reduceSub, Nat.mul_one] using hD
  | @node n ranges L R ihL ihR =>
    have hL := ihL hD.2.1
    have hR := ihR hD.2.2
    have hp := Nat.one_le_two_pow (n := n + 1)
    change ranges.length + L.count + R.count ≤ K * (2 ^ (n + 1 + 1) - 1)
    rw [pow_succ]
    have he : 2 ^ (n + 1) * 2 - 1 = (2 ^ (n + 1) - 1) * 2 + 1 := by omega
    rw [he]
    nlinarith only [hD.1, hL, hR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original atom-product and word-bin ranges on the expanded schedule -/

namespace Ostmann

open scoped Classical

theorem ScheduleAtomRange.toWord_length {I σ : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (current : CopyScheduleAtoms role n → List σ)
    (A M : ℕ) (hr : r.atoms.length ≤ A) (hc : ∀ i, (current i).length ≤ M) :
    (r.toWord current).word.length ≤ A * M := by
  exact (list_flatMap_length_bound r.atoms current M (fun i _ => hc i)).trans
    (Nat.mul_le_mul_right M hr)

/-- The range count is controlled at every stage, including the terminal bins. -/
theorem expandedScheduleRanges_count_bounded {I σ : Type*} (role : I → CopyScheduleRole)
    (address : ℕ → List Bool → σ) (ranges : (n : ℕ) → List (ScheduleAtomRange role n))
    (n K : ℕ) (hK : ∀ j ≤ n, (ranges j).length ≤ K)
    (path : List Bool) (current : CopyScheduleAtoms role n → List σ) :
    (expandedScheduleRanges role address ranges n path current).CountBounded K := by
  induction n generalizing path with
  | zero => simpa only [expandedScheduleRanges, WordRangeDecoration.CountBounded, List.length_map]
      using hK 0 le_rfl
  | succ n ih =>
    exact ⟨by simpa only [List.length_map] using hK (n + 1) le_rfl,
      ih (fun j hj => hK j (by omega)) _ _, ih (fun j hj => hK j (by omega)) _ _⟩

/-- Products in all original range tests have the same finite word bound
as their actual constituent expansion. -/
theorem expandedScheduleRanges_words_bounded {I σ : Type*} (role : I → CopyScheduleRole)
    (address : ℕ → List Bool → σ) (ranges : (n : ℕ) → List (ScheduleAtomRange role n))
    (n A M : ℕ) (hM : 1 ≤ M)
    (hA : ∀ j ≤ n, ∀ r ∈ ranges j, r.atoms.length ≤ A)
    (path : List Bool) (current : CopyScheduleAtoms role n → List σ)
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedScheduleRanges role address ranges n path current).WordsBounded (A * M + 1) := by
  induction n generalizing path with
  | zero =>
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact Nat.add_le_add_right (q.toWord_length current A M (hA 0 le_rfl q hq) hc) 1
  | succ n ih =>
    refine ⟨?_, ih (fun j hj => hA j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n true _ current M hM hc),
      ih (fun j hj => hA j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n false _ current M hM hc)⟩
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact Nat.add_le_add_right (q.toWord_length current A M (hA (n + 1) le_rfl q hq) hc) 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPrimeBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derived size, integrality and denominator bounds for the prime checks -/

namespace Ostmann

open scoped Classical

theorem WordPrimeDecoration.count_le {V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (K : ℕ) (hD : D.CountBounded K) :
    D.count ≤ K * (2 ^ n - 1) := by
  induction D with
  | leaf => simp only [count, pow_zero, Nat.sub_self, Nat.mul_zero, le_refl]
  | @node n coordinates L R ihL ihR =>
    have hL := ihL hD.2.1
    have hR := ihR hD.2.2
    have hp := Nat.one_le_two_pow (n := n)
    change coordinates.length + L.count + R.count ≤ K * (2 ^ (n + 1) - 1)
    rw [pow_succ]
    have he : 2 ^ n * 2 - 1 = (2 ^ n - 1) * 2 + 1 := by omega
    rw [he]
    nlinarith only [hD.1, hL, hR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedPrimeCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete Y-prime check count is polynomial in the original word size -/

namespace Ostmann

open scoped Classical

theorem expandedYPrimeCoordinates_length {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n M : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedYPrimeCoordinates role depth n current).length ≤
      3 ^ n * Fintype.card I * M := by
  have hY : Fintype.card (CopyScheduleY role n) ≤ 3 ^ n * Fintype.card I := by
    rw [← copyScheduleVertex_card n]
    exact Fintype.card_subtype_le _
  apply (list_flatMap_length_bound _ _ M (fun i _ =>
    (expandedOriginalWord_length _).trans (hc ⟨.inr i.val, i.property⟩))).trans
  simpa only [Finset.length_toList, Finset.card_univ] using Nat.mul_le_mul_right M hY

theorem expandedSchedulePrimes_count_bounded {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n M : ℕ) (hn : n ≤ depth) (hM : 1 ≤ M)
    (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable V depth))
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedSchedulePrimes role depth n path current).CountBounded
      (3 ^ depth * Fintype.card I * M) := by
  induction n generalizing path with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_, ih (by omega) _ _ (reverseCopyLabelMap_list_length role n true _ current M hM hc),
      ih (by omega) _ _ (reverseCopyLabelMap_list_length role n false _ current M hM hc)⟩
    exact (expandedYPrimeCoordinates_length role depth n M current hc).trans
      (Nat.mul_le_mul_right M (Nat.mul_le_mul_right (Fintype.card I)
        (Nat.pow_le_pow_right (by omega) (by omega))))

theorem expandedRootPrimes_count {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n M : ℕ) (hM : 1 ≤ M)
    (words : CopyScheduleAtoms role n → List V) (hw : ∀ i, (words i).length ≤ M) :
    (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl)).count ≤
      (3 ^ n * Fintype.card I * M) * (2 ^ n - 1) := by
  exact WordPrimeDecoration.count_le _ _
    (expandedSchedulePrimes_count_bounded role n n M le_rfl hM [] _
      (fun i => by simpa only [List.length_map] using hw i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_TotalAtomUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual unit condition on every current atom at every frequency -/

namespace Ostmann

open scoped BigOperators Classical

/-- A unit product is exactly the original assertion that every current
atom is a unit. The dummy interval endpoints play no part in this test. -/
theorem totalAtomUnitRanges_iff {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (s : ℤ) :
    (∀ r ∈ totalAtomUnitRanges role n, ((r.atoms.map x).prod).Coprime s.natAbs) ↔
      ∀ i, (x i).Coprime s.natAbs := by
  simp only [totalAtomUnitRanges, List.mem_singleton, forall_eq]
  rw [Finset.prod_map_toList]
  exact Nat.coprime_fintype_prod_left_iff

theorem WordRangeDecoration.wordsBounded_mono {σ : Type*} {n B C : ℕ}
    (D : WordRangeDecoration σ n) (hD : D.WordsBounded B) (hBC : B ≤ C) : D.WordsBounded C := by
  induction D with
  | leaf ranges => exact fun r hr => (hD r hr).trans hBC
  | node ranges L R ihL ihR => exact ⟨fun r hr => (hD.1 r hr).trans hBC, ihL hD.2.1, ihR hD.2.2⟩

theorem copyScheduleAtoms_card_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleAtoms role n) ≤ 3 ^ n * Fintype.card I := by
  rw [← copyScheduleVertex_card n]
  exact Fintype.card_subtype_le _

/-- Its product words fit the same concrete bound as the Fourier template. -/
theorem totalAtomUnits_words_bounded {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (M : ℕ) (hM : 1 ≤ M) (hwords : ∀ i, (words i).length ≤ M) :
    (expandedRootRanges role n words (totalAtomUnitRanges role)).WordsBounded
      (2 * 3 ^ n * Fintype.card I * M + 4) := by
  have hA : ∀ j ≤ n, ∀ r ∈ totalAtomUnitRanges role j,
      r.atoms.length ≤ 3 ^ n * Fintype.card I := by
    intro j hj r hr
    have he : r = ⟨Finset.univ.toList, 0, 0⟩ := List.mem_singleton.mp hr
    subst r
    simp only [Finset.length_toList, Finset.card_univ]
    exact (copyScheduleAtoms_card_le role j).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hj))
  have hh := expandedScheduleRanges_words_bounded role (expandedPivotAddress V n)
    (totalAtomUnitRanges role) n (3 ^ n * Fintype.card I) M hM hA []
    (fun i => (words i).map Sum.inl) (fun i => by simpa only [List.length_map] using hwords i)
  exact WordRangeDecoration.wordsBounded_mono _ hh (by nlinarith only [Nat.zero_le (3 ^ n * Fintype.card I * M)])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SchedulePairwiseReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reduced support implies every original pairwise-coprimality gate -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduleAtomUnitsValid_root {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n x t) :
    ∀ i, (x i).Coprime (frequencyRoot n t).natAbs := by
  cases n with
  | zero => exact (totalAtomUnitRanges_iff role 0 x t).mp hu
  | succ n => exact (totalAtomUnitRanges_iff role (n + 1) x t.1).mp hu.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleFullCoprime
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the complete large-coprimality support from the reduced tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem schedule_full_coprime_reduced {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : scheduleAtomFullCoprimeValid role childBound pivotBound n x t) :
    Pairwise (fun i j => (x i).Coprime (x j)) ∧
      scheduleAtomCoprimalitiesValid role childBound pivotBound n x t := by
  induction n with
  | zero => exact ⟨h, trivial⟩
  | succ n ih =>
    exact ⟨h.1, (fun i => (h.2.1 _).symm), (ih _ _ h.2.2.1).2,
      (ih _ _ h.2.2.2).2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete grouped weight as a single supported recursive weight -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem fullAtomWeightGuard_node {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j)) (n : ℕ)
    (x : CopyScheduleAtoms role (n + 1) → ℕ) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    fullAtomWeightGuard role childBound pivotBound ranges (n + 1) x t ↔
      fullAtomRootGuard role ranges n x P t.1 ∧
      fullAtomWeightGuard role childBound pivotBound ranges n (reverseCopyLabelMap role n true P x) t.2.1 ∧
      fullAtomWeightGuard role childBound pivotBound ranges n (reverseCopyLabelMap role n false P x) t.2.2 := by
  simp only [fullAtomWeightGuard, scheduleAtomFullCoprimeValid, scheduleAtomUnitsValid,
    scheduleAtomRangesValid, hP.historyPivot_eq, totalAtomUnitRanges_iff, fullAtomRootGuard]
  tauto

private theorem guarded_product (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] (x y : ℂ) :
    (if A ∧ B ∧ C then x * conj y else 0) =
      if A then (if B then x else 0) * conj (if C then y else 0) else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC]

/-- The full weight has exactly the inherited left/right factors, with all
new top tests in the root guard. There is no loss of boundary or unit tests. -/
theorem fullAtomTransferWeight_node {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role (n + 1) → ℕ) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1) x t =
      if fullAtomRootGuard role ranges n x P t.1 then
        fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (reverseCopyLabelMap role n true P x) t.2.1 *
        conj (fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (reverseCopyLabelMap role n false P x) t.2.2) else 0 := by
  simp only [fullAtomTransferWeight,
    fullAtomWeightGuard_node role childBound pivotBound ranges n x t P hP,
    recursiveTransferWeight_node _ leaf _ n ⟨n + 1, x⟩ t P hP,
    Complex.ofReal_one, one_mul]
  exact guarded_product _ _ _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomWeightSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support and square-energy bounds for the actual full atom weight -/

namespace Ostmann

open scoped BigOperators Classical

theorem fullAtomTransferWeight_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0) :
    fullAtomWeightGuard role childBound pivotBound ranges n x t ∧
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, x⟩ t := by
  unfold fullAtomTransferWeight at h
  split_ifs at h with hg
  · exact ⟨hg, recursiveTransferWeight_nonzero_valid _ _ _ _ _ _ h⟩
  · exact False.elim (h rfl)

theorem fullAtomTransferWeight_top_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0) :
    Pairwise (fun i j => (x i).Coprime (x j)) ∧
      (∀ i, (x i).Coprime (frequencyRoot n t).natAbs) := by
  have hg := (fullAtomTransferWeight_support role childBound pivotBound ranges leaf n x t h).1
  exact ⟨(schedule_full_coprime_reduced role childBound pivotBound n x t hg.1).1,
    scheduleAtomUnitsValid_root role childBound pivotBound n x t hg.2.1⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_AtomIntervalComplexity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original interval guards have bounded complexity at every finite depth -/
namespace Ostmann
open scoped Classical

theorem atomIntervalRanges_singleton {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ) (n : ℕ)
    (r : ScheduleAtomRange role n) (hr : r ∈ atomIntervalRanges role lo hi n) :
    r.atoms.length = 1 := by
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
  rfl

theorem atomIntervalRanges_length_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ) (k n : ℕ) (hn : n ≤ k) :
    (atomIntervalRanges role lo hi n).length ≤ 3 ^ k * Fintype.card I := by
  have he : (atomIntervalRanges role lo hi n).length = Fintype.card (CopyScheduleAtoms role n) := by
    simp only [atomIntervalRanges, List.length_map, Finset.length_toList, Finset.card_univ]
  rw [he]
  exact (copyScheduleAtoms_card_le role n).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega : 1 ≤ 3) hn))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_LeafFrequencyBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The remaining leaf-frequency budget in the norm comparison -/

namespace Ostmann

theorem sqrt_cost_sublinear (A B ε : ℝ) (_hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → A * Real.sqrt m + B ≤ ε * m := by
  refine ⟨max ((2 * A / ε) ^ 2) (2 * max B 0 / ε), fun m hm => ?_⟩
  have hmA : (2 * A / ε) ^ 2 ≤ m := (le_max_left _ _).trans hm
  have hmB : 2 * max B 0 / ε ≤ m := (le_max_right _ _).trans hm
  have hm0 : 0 ≤ m := (sq_nonneg _).trans hmA
  have hr := Real.le_sqrt_of_sq_le hmA
  have hA' : A ≤ ε / 2 * Real.sqrt m := by
    have h := (div_le_iff₀ hε).mp hr
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hA' (Real.sqrt_nonneg m)
  have hsq := Real.sq_sqrt hm0
  have hB' : B ≤ ε / 2 * m := by
    have h := (div_le_iff₀ hε).mp hmB
    have hmax := le_max_left B 0
    nlinarith
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SampledTupleAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite graph amplitude of an injective prime sample -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

theorem prime_character_isPrimitive (p : ℕ) (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) : χ.IsPrimitive := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with h | h
  · exact False.elim (hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  · exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FactorialExponential
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary exponential factorial bounds used in arrangement ratios -/

namespace Ostmann

theorem factorial_exp_lower {n : ℕ} (hn : 1 ≤ n) :
    Real.exp ((n : ℝ) * Real.log n - n) ≤ (n.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (show n ≠ 0 by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.two_le_pi])
  calc
    _ ≤ Real.exp (Real.log (n.factorial : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_log (by exact_mod_cast Nat.factorial_pos n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OneSidedDecayBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated long/short scales absorb the one-sided losses -/

namespace Ostmann

open Filter

theorem eventual_polynomial_log_budget (C z α ε : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 0 ≤ m → m ≤ z * L →
      C * (1 + m) ^ d ≤ ε * Real.exp (α * L) := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop d hα).const_mul_left
    (C * (z + 1) ^ d)).bound hε
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hlarge hL m hm hmL
  have hx : 1 + m ≤ (z + 1) * L := by nlinarith
  have hp : (1 + m) ^ d ≤ ((z + 1) * L) ^ d := pow_le_pow_left₀ (by linarith) hx d
  have hlarge' : C * (z + 1) ^ d * L ^ d ≤ ε * Real.exp (α * L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ C * (z + 1) ^ d * L ^ d),
      abs_of_pos (Real.exp_pos _)] using hlarge
  calc
    _ ≤ C * (((z + 1) * L) ^ d) := mul_le_mul_of_nonneg_left hp hC
    _ = C * (z + 1) ^ d * L ^ d := by rw [mul_pow]; ring
    _ ≤ _ := hlarge'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalHistoryCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-depth cost of summing both frequency histories -/

namespace Ostmann

open scoped BigOperators
open Filter

theorem card_frequencyTree (A : Type) [Fintype A] (n : ℕ) :
    Fintype.card (FrequencyTree A n) = (Fintype.card A) ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simp [FrequencyTree]
  | succ n ih =>
    simp only [FrequencyTree, Fintype.card_prod] at *
    rw [ih, ← pow_add, ← pow_succ']
    congr 1
    have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    rw [pow_succ]
    omega

theorem frequency_history_pair_card_bound (S : Finset ℤ) (n : ℕ) (C m : ℝ)
    (hS : (S.card : ℝ) ≤ Real.exp (C * m)) :
    ((Fintype.card (FrequencyTree S n) : ℝ) ^ 2) ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * C * m) := by
  rw [card_frequencyTree]
  simp only [Fintype.card_coe]
  push_cast
  rw [← pow_mul]
  have h := pow_le_pow_left₀ (Nat.cast_nonneg S.card) hS ((2 ^ (n + 1) - 1) * 2)
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFrequencyBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete rounded frequency family and its finite counting cost -/

namespace Ostmann

open scoped BigOperators Classical

theorem transferErrorScale_monotone (Δ m : ℝ) (hΔ : 0 ≤ Δ) : Monotone (transferErrorScale Δ m) := by
  apply monotone_nat_of_le_succ
  intro n
  have h2 : 0 ≤ (2 : ℝ) ^ n * Δ := mul_nonneg (by positivity) hΔ
  have h4 : 0 ≤ (4 : ℝ) ^ n * Real.sqrt m := mul_nonneg (by positivity) (Real.sqrt_nonneg m)
  simp only [transferErrorScale, pow_succ]
  nlinarith

theorem naturalTransferCutoff_monotone (Δ m : ℝ) (hΔ : 0 ≤ Δ) :
    Monotone (naturalTransferCutoff Δ m) := by
  intro a b hab
  exact Nat.floor_le_floor (Real.exp_le_exp.mpr (transferErrorScale_monotone Δ m hΔ hab))

theorem transferFrequencyRange_mono : Monotone transferFrequencyRange := by
  intro a b hab s hs
  exact (mem_transferFrequencyRange b s).mpr (((mem_transferFrequencyRange a s).mp hs).trans hab)

theorem scheduledFrequencyIndex_card_le (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ) :
    Fintype.card (ScheduledFrequencyIndex V n) ≤
      (transferFrequencyRange (V n)).card ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero =>
    have he : ScheduledFrequencyIndex V 0 ≃ transferFrequencyRange (V 0) := Equiv.refl _
    have hc := Fintype.card_congr he
    simpa only [Fintype.card_coe, Nat.zero_add, pow_one, Nat.reducePow, Nat.reduceSub] using hc.le
  | succ n ih =>
    have hc := Finset.card_le_card (transferFrequencyRange_mono (hV (Nat.le_succ n)))
    have hh := ih.trans (Nat.pow_le_pow_left hc (2 ^ (n + 1) - 1))
    have he : ScheduledFrequencyIndex V (n + 1) ≃
        (transferFrequencyRange (V (n + 1))) × (ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n) :=
      Equiv.refl _
    have hcard := Fintype.card_congr he
    simp only [Fintype.card_prod, Fintype.card_coe] at hcard
    rw [hcard]
    calc
      _ ≤ (transferFrequencyRange (V (n + 1))).card *
          ((transferFrequencyRange (V (n + 1))).card ^ (2 ^ (n + 1) - 1) *
           (transferFrequencyRange (V (n + 1))).card ^ (2 ^ (n + 1) - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hh hh)
      _ = _ := by
        rw [← pow_add, ← pow_succ']
        congr 1
        have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
        rw [pow_succ]
        omega

theorem scheduledFrequencyIndex_pair_card_bound (V : ℕ → ℕ) (hV : Monotone V)
    (n : ℕ) (C m : ℝ) (hS : ((transferFrequencyRange (V n)).card : ℝ) ≤ Real.exp (C * m)) :
    (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * C * m) := by
  have hc : Fintype.card (ScheduledFrequencyIndex V n) ≤
      Fintype.card (FrequencyTree (transferFrequencyRange (V n)) n) := by
    rw [card_frequencyTree, Fintype.card_coe]
    exact scheduledFrequencyIndex_card_le V hV n
  exact (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hc) 2).trans
    (frequency_history_pair_card_bound (transferFrequencyRange (V n)) n C m hS)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPrimeFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural character-frequency cutoffs lie below the actual prime ranges -/
namespace Ostmann
open Filter

/-- A fixed depth has a linear exponent, including the rounded bottom cutoff
with its original factor two in front of sqrt(m). -/
theorem transferErrorScale_linear_bound (k j : ℕ) (d m : ℝ)
    (hj : j ≤ k) (hd : 0 ≤ d) (hm : 1 ≤ m) :
    transferErrorScale (d * m) m j ≤ ((2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k) * m := by
  have hs : Real.sqrt m ≤ m := (Real.sqrt_le_iff).mpr ⟨by linarith, by nlinarith⟩
  have htwo : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have hfour : (4 : ℝ) ^ j ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hj
  have hfirst := mul_le_mul_of_nonneg_right htwo (mul_nonneg hd (by linarith : 0 ≤ m))
  have hsecond := mul_le_mul hfour hs (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 4 ^ k)
  unfold transferErrorScale
  nlinarith only [hfirst, hsecond]

/-- This supplies both the prime-frequency separation and the finite powers
of the cutoff used for denominator removal in the selected energy estimate. -/
theorem eventual_natural_cutoff_power_lt (k r : ℕ) (d z α c : ℝ)
    (hd : 0 ≤ d) (_hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L → ∀ j ≤ k,
      (((naturalTransferCutoff (d * m) m j) ^ r : ℕ) : ℝ) <
        Real.exp (c * Real.exp (α * L)) := by
  let D := (2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 1 hα).const_mul_left ((r : ℝ) * D * z)).bound
    (by positivity : 0 < c / 2)
  filter_upwards [hb] with L hL m hm hmL j hj
  have hlin : (r : ℝ) * D * z * L < c * Real.exp (α * L) := by
    have hh : |(r : ℝ) * D * z * L| ≤ c / 2 * Real.exp (α * L) := by
      simpa only [Real.norm_eq_abs, pow_one, abs_of_pos (Real.exp_pos _)] using hL
    have hn := le_abs_self ((r : ℝ) * D * z * L)
    nlinarith only [hh, hn, Real.exp_pos (α * L), hc]
  have hscale := transferErrorScale_linear_bound k j d m hj hd hm
  have hm' := mul_le_mul_of_nonneg_left hmL (mul_nonneg (Nat.cast_nonneg r) hD)
  have he : (r : ℝ) * transferErrorScale (d * m) m j < c * Real.exp (α * L) := by
    change transferErrorScale (d * m) m j ≤ D * m at hscale
    have hs := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg (α := ℝ) r)
    nlinarith only [hs, hm', hlin]
  calc
    _ = (naturalTransferCutoff (d * m) m j : ℝ) ^ r := by simp only [Nat.cast_pow]
    _ ≤ (Real.exp (transferErrorScale (d * m) m j)) ^ r :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.floor_le (Real.exp_pos _).le) r
    _ = Real.exp ((r : ℝ) * transferErrorScale (d * m) m j) := (Real.exp_nat_mul _ _).symm
    _ < _ := Real.exp_lt_exp.mpr he

theorem eventual_natural_cutoff_below_primes (k : ℕ) (d z α c : ℝ)
    (hd : 0 ≤ d) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L →
      ∀ p : ℕ, Real.exp (c * Real.exp (α * L)) ≤ p →
        ∀ j ≤ k, naturalTransferCutoff (d * m) m j < p := by
  filter_upwards [eventual_natural_cutoff_power_lt k 1 d z α c hd hz hα hc] with L hL
  intro m hm hmL p hp j hj
  have hh := (hL m hm hmL j hj).trans_le hp
  simpa only [pow_one, Nat.cast_lt] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFourierBudgets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit finite-frequency and Fourier-window costs -/
namespace Ostmann
open scoped Classical
open scoped FourierTransform SchwartzMap

theorem naturalTransferCutoff_linear_bound (k j : ℕ) (d m : ℝ)
    (hj : j ≤ k) (hd : 0 ≤ d) (hm : 1 ≤ m) :
    (naturalTransferCutoff (d * m) m j : ℝ) ≤
      Real.exp (((2 : ℝ) ^ k * d + 2 * (4 : ℝ) ^ k) * m) := by
  exact (Nat.floor_le (Real.exp_nonneg _)).trans
    (Real.exp_le_exp.mpr (transferErrorScale_linear_bound k j d m hj hd hm))

theorem character_initial_window_bounds (d C m : ℝ)
    (hd : 1 ≤ d) (hm : 1 ≤ m) (hC : 0 ≤ C) (hCm : C ≤ m) :
    1 ≤ Real.exp (d * m - C) ∧
      Real.exp (d * m - C) ≤ Real.exp (d * m + C) ∧
      Real.exp (d * m + C) - Real.exp (d * m - C) ≤ Real.exp ((d + 1) * m) := by
  have hm0 : 0 ≤ m := by linarith
  have hdm : m ≤ d * m := by nlinarith only [hd, hm0]
  refine ⟨Real.one_le_exp_iff.mpr (by linarith),
    Real.exp_le_exp.mpr (by linarith), ?_⟩
  apply (sub_le_self _ (Real.exp_nonneg _)).trans
  exact Real.exp_le_exp.mpr (by nlinarith only [hCm])

theorem character_prime_band_log_ratio (α β L M H : ℝ)
    (hL : 0 ≤ L) (hLM : L ≤ M) (_hβ : 0 ≤ β) (hH : β - α ≤ H) (hH0 : 0 ≤ H) :
    Real.log (Real.exp (Real.exp (β * L))) / Real.exp (α * L) ≤
      Real.exp (H * (1 + M)) := by
  rw [Real.log_exp, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right hH hL
  have h₂ := mul_le_mul_of_nonneg_left hLM hH0
  nlinarith only [h₁, h₂, hH0]

theorem character_prime_band_dyadic_budget (E : ℕ) (β L M H : ℝ)
    (hβ : 0 ≤ β) (hL : 1 ≤ L) (hLM : L ≤ M)
    (hH : β + Real.log ((Real.log 2)⁻¹ + 1) ≤ H) (hH0 : 0 ≤ H)
    (hE : (E : ℝ) ≤ Real.exp (Real.exp (β * L))) :
    ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)) := by
  apply (dyadic_prime_range_count E β L hβ hL hE).trans
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right hH (by linarith : 0 ≤ L)
  have h₂ := mul_le_mul_of_nonneg_left hLM hH0
  nlinarith only [h₁, h₂, hH0]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterBandCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer endpoints for the separated character prime bands -/
namespace Ostmann
open Filter

/-- A fixed positive gap in log-log scale supplies the factor two required
by the one-sided character estimate, even after rounding upward. -/
theorem eventual_double_exp_integer_margin (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop,
      2 * (⌈Real.exp (Real.exp (α * L))⌉₊ : ℝ) ≤ Real.exp (Real.exp (β * L)) := by
  filter_upwards [arithmetic_exponent_absorption α β 0 4 1 0 hβ hαβ hβ (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hgap hL
  simp only [pow_zero, zero_mul, Real.exp_zero, one_mul] at hgap
  have hlog4 : Real.log 4 ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hm := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg (α * L))
  have he : Real.log 4 + Real.exp (α * L) ≤ Real.exp (β * L) := by
    nlinarith only [hgap, hm, Real.exp_nonneg (α * L), hlog4]
  have hceil := (Nat.ceil_lt_add_one (Real.exp_nonneg (Real.exp (α * L)))).le
  have hexp : 1 ≤ Real.exp (Real.exp (α * L)) :=
    Real.one_le_exp (Real.exp_nonneg _)
  calc
    _ ≤ 4 * Real.exp (Real.exp (α * L)) := by linarith
    _ = Real.exp (Real.log 4 + Real.exp (α * L)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem eventual_character_band_lower (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop,
      let A := ⌈Real.exp (Real.exp (α * L))⌉₊
      0 < A ∧ Real.exp (Real.exp (α * L)) ≤ A ∧
        ∀ p : ℕ, Real.exp (Real.exp (β * L)) ≤ p → 2 * A ≤ p := by
  filter_upwards [eventual_double_exp_integer_margin α β hβ hαβ] with L hL
  refine ⟨Nat.ceil_pos.mpr (Real.exp_pos _), Nat.le_ceil _, ?_⟩
  intro p hp
  exact_mod_cast hL.trans hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullWeightFrequencies
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero frequencies from the actual unit and modulus-window support -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem fullAtomTransferWeight_all_frequencies_ne_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  induction n with
  | zero =>
    intro s hs
    have he : s = t := by simpa only [allFrequencyList, List.mem_singleton] using hs
    subst s
    intro ht
    subst t
    exact hw (hzero x)
  | succ n ih =>
    obtain ⟨hg, P, hP, _, _⟩ := fullAtomTransferWeight_support role childBound pivotBound ranges leaf
      (n + 1) x t hw
    have hr := ((fullAtomWeightGuard_node role childBound pivotBound ranges n x t P hP).mp hg).1
    rw [fullAtomTransferWeight_node role childBound pivotBound ranges leaf n x t P hP,
      ite_eq_left hr] at hw
    obtain ⟨hL, hR⟩ := mul_ne_zero_iff.mp hw
    have hR' : fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (reverseCopyLabelMap role n false P x) t.2.2 ≠ 0 := by
      intro hz
      exact hR (by rw [hz, map_zero])
    intro s hs
    rcases List.mem_cons.mp hs with he | hs
    · exact he ▸ hP.root_ne_zero
    · rcases List.mem_append.mp hs with hs | hs
      · exact ih _ t.2.1 hL s hs
      · exact ih _ t.2.2 hR' s hs

/-- A zero bottom frequency would make every atom equal to one. The actual
initial modulus window excludes that case, including at its endpoints. -/
theorem fullAtomFourierWeight_zero_frequency {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hlo : 1 < X * lo)
    (x : CopyScheduleAtoms role 0 → ℕ) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X))
      0 x (0 : ℤ) = 0 := by
  by_contra hw
  have hu := (fullAtomTransferWeight_top_support role childBound pivotBound ranges _ 0 x (0 : ℤ) hw).2
  have hx (i) : x i = 1 := by simpa only [frequencyRoot, Int.natAbs_zero, Nat.coprime_zero_right] using hu i
  have ht : scheduleAtomTotal role ⟨0, x⟩ = 1 := by
    simp only [scheduleAtomTotal, hx, Finset.prod_const_one]
  have hm : ¬ (scheduleAtomTotal role ⟨0, x⟩ : ℝ) / X ∈ Set.Icc lo hi := by
    intro hm
    have h := (le_div_iff₀ hX).mp hm.1
    rw [ht, Nat.cast_one] at h
    nlinarith
  apply hw
  unfold fullAtomTransferWeight
  split_ifs
  · simp only [recursiveTransferWeight, hm, ite_false, if_false, zero_mul]
  · rfl

theorem fullAtomFourierWeight_all_frequencies_ne_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hlo : 1 < X * lo)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  exact fullAtomTransferWeight_all_frequencies_ne_zero role childBound pivotBound ranges _
    (fullAtomFourierWeight_zero_frequency role childBound pivotBound ranges ψ X lo hi hX hlo) n x t hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialGaussMultipliers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bounded Gauss multipliers for every original prime role -/

namespace Ostmann
open scoped Classical

theorem primeGaussMultiplier_norm (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (p : ℕ) :
    ‖primeGaussMultiplier χ p‖ = 1 := by
  unfold primeGaussMultiplier
  split_ifs with hp
  · exact @primitiveGaussPhase_norm p ⟨hp.1.ne_zero⟩ _
      (prime_character_isPrimitive p hp.1 (χ p) hp.2)
  · exact norm_one

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterScheduleRoles
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite role set used in the nonquadratic character argument

A positive word, finitely many pivot groups, two fresh anchors at each step,
and one filler have independent negative copies. Only the positive word,
pivots and anchors participate in the copy schedule.
-/
namespace Ostmann
open scoped Classical BigOperators

theorem characterPivotAtom_unique {k : ℕ} (j : Fin k) (v : CharacterRole k)
    (hv : characterRole k v = .pivot j.val) : v = characterPivotAtom j := by
  rcases v with ⟨b, c⟩
  cases b with
  | false => simp [characterRole, signedAtomRole] at hv
  | true =>
    cases c with
    | none => simp [characterRole, signedAtomRole, characterPositiveRole] at hv
    | some c =>
      rcases c with i | a | u
      · have hi : i = j := Fin.ext (CopyScheduleRole.pivot.inj hv)
        subst i
        rfl
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hv
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterComparisonCounts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete complexity bounds for the signed character comparison -/
namespace Ostmann
open scoped Classical

theorem characterSize_le (k m N : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (hr : ∀ j, r j ≤ N) (hf : f ≤ N) (v : CharacterRole k) :
    characterSize m r f v ≤ m + N + 1 := by
  rcases v with ⟨b, v⟩
  cases v with
  | none => change m + 1 ≤ _; omega
  | some v =>
    rcases v with j | (a | u)
    · exact (hr j).trans (by omega)
    · change 1 ≤ _; omega
    · exact hf.trans (by omega)

theorem characterSize_linear_bound (m N : ℕ) :
    ((m + N + 1 : ℕ) : ℝ) ≤ ((N : ℝ) + 2) * (1 + (m : ℝ)) := by
  have hm := Nat.cast_nonneg (α := ℝ) m
  have hN := Nat.cast_nonneg (α := ℝ) N
  push_cast
  nlinarith

theorem character_interval_complexity (k n : ℕ) (hn : n ≤ k)
    (lo hi : CharacterRole k → ℕ) :
    (∀ j ≤ n, ∀ r ∈ atomIntervalRanges (characterRole k) lo hi j, r.atoms.length ≤ 1) ∧
      ∀ j ≤ n, (atomIntervalRanges (characterRole k) lo hi j).length ≤
        3 ^ k * Fintype.card (CharacterRole k) := by
  refine ⟨fun j _ r hr => (atomIntervalRanges_singleton _ lo hi j r hr).le, ?_⟩
  intro j hj
  exact atomIntervalRanges_length_le _ lo hi k j (hj.trans hn)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterEnergyPrimeRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic data for the actual prime-cell energy theorem -/
namespace Ostmann
open Filter

 theorem naturalTransferCutoff_pos (d m : ℝ) (hd : 0 ≤ d) (hm : 0 ≤ m) (j : ℕ) :
    0 < naturalTransferCutoff (d * m) m j := by
  apply Nat.floor_pos.mpr
  apply Real.one_le_exp_iff.mpr
  unfold transferErrorScale
  positivity

theorem eventual_twice_natural_cutoff_power_le (k r : ℕ) (d z α : ℝ)
    (hd : 0 ≤ d) (hz : 0 ≤ z) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L →
      ∀ A : ℕ, Real.exp (Real.exp (α * L)) ≤ A → ∀ j ≤ k,
        2 * naturalTransferCutoff (d * m) m j ^ r ≤ A := by
  have hg : ∀ᶠ L : ℝ in atTop, 2 * Real.log 2 ≤ Real.exp (α * L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hα)).eventually
      (eventually_ge_atTop _)
  filter_upwards [hg, eventual_natural_cutoff_power_lt k r d z α (1 / 2)
    hd hz hα (by norm_num)] with L hg hcut
  intro m hm hmL A hA j hj
  have he : 2 * Real.exp ((1 / 2 : ℝ) * Real.exp (α * L)) ≤
      Real.exp (Real.exp (α * L)) := by
    calc
      _ = Real.exp (Real.log 2 + (1 / 2 : ℝ) * Real.exp (α * L)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hc := mul_le_mul_of_nonneg_left (hcut m hm hmL j hj).le (by norm_num : (0 : ℝ) ≤ 2)
  have hf := hc.trans (he.trans hA)
  exact_mod_cast hf

/-- Both dyadic endpoints are explicit ceilings/floors of the physical prime
range. The finite denominator power is below the first dyadic point. -/
theorem eventual_character_energy_prime_range (k r : ℕ) (d z α β : ℝ)
    (hd : 0 ≤ d) (hz : 0 ≤ z) (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ᶠ L : ℝ in atTop, ∀ m : ℝ, 1 ≤ m → m ≤ z * L →
      ∀ S : Finset ℕ,
      (∀ p ∈ S, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (β * L))) →
      ∃ h J : ℕ,
        (∀ j ≤ k, naturalTransferCutoff (d * m) m j ^ r ≤ 2 ^ h) ∧
        (∀ p ∈ S, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) ∧
        (J : ℝ) ≤ Real.exp ((β + Real.log ((Real.log 2)⁻¹ + 1)) * L) := by
  filter_upwards [eventual_twice_natural_cutoff_power_le k r d z α hd hz hα,
    eventually_ge_atTop (1 : ℝ)] with L hcut hL
  intro m hm hmL S hS
  let A : ℕ := ⌈Real.exp (Real.exp (α * L))⌉₊
  let B : ℕ := ⌊Real.exp (Real.exp (β * L))⌋₊
  have hbounds : ∀ p ∈ S, A ≤ p ∧ p ≤ B := by
    intro p hp
    exact ⟨Nat.ceil_le.mpr (hS p hp).1, Nat.le_floor (hS p hp).2⟩
  have hA : Real.exp (Real.exp (α * L)) ≤ (A : ℝ) := Nat.le_ceil _
  have hq (j : ℕ) : 0 < naturalTransferCutoff (d * m) m j ^ r :=
    pow_pos (naturalTransferCutoff_pos d m hd (by linarith) j) r
  have hranges (j : ℕ) (hj : j ≤ k) := dyadic_prime_range_cover A B
    (naturalTransferCutoff (d * m) m j ^ r) (hq j) (hcut m hm hmL A hA j hj) S hbounds
  refine ⟨Nat.log 2 A, Nat.log 2 B + 1, fun j hj => (hranges j hj).1,
    (hranges 0 (Nat.zero_le _)).2, ?_⟩
  exact dyadic_prime_range_count B β L hβ hL (Nat.floor_le (Real.exp_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledMatchedEdges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The anchor interaction in the literal retained matching graph -/

namespace Ostmann
open scoped Classical

/-- This is an identity for the computed graph, with the counterpart slot
identified by the actual inverse matching permutation. -/
theorem scheduledMatchedGraph_anchor_word {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (a i i' : I) (j : Fin (n + 1)) (ha : role a = .anchor j) (b : Bool)
    (hap : ∀ k < n + 1, a ≠ pivot k) (hai : a ≠ i) (hai' : a ≠ i')
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i') :
    scheduledMatchedGraph role pivot (n + 1) e
      (.inr (scheduledPastAnchor role n a j ha b)) (.inl h) =
      anchorIncoming (fun _ => 1) t j b - anchorIncoming (fun _ => 1) t' j b := by
  change copyScheduleGraph initialCompleteGraph pivot (n + 1)
      (copyScheduleAnchor (n + 1) j b a) h.val -
    copyScheduleGraph initialCompleteGraph pivot (n + 1)
      (copyScheduleAnchor (n + 1) j b a) (e.symm h).val = _
  rw [hh, hh', copyScheduleGraph_anchor_to_path, copyScheduleGraph_anchor_to_path]
  · exact fun k hk => initialCompleteGraph_of_ne (hap k hk)
  · exact initialCompleteGraph_of_ne hai'
  · exact fun k hk => initialCompleteGraph_of_ne (hap k hk)
  · exact initialCompleteGraph_of_ne hai

theorem scheduledMatchedGraph_word_anchor {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (a i i' : I) (j : Fin (n + 1)) (ha : role a = .anchor j) (b : Bool)
    (hip : ∀ k < n + 1, i ≠ pivot k) (hi'p : ∀ k < n + 1, i' ≠ pivot k)
    (hia : i ≠ a) (hi'a : i' ≠ a)
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i') :
    scheduledMatchedGraph role pivot (n + 1) e
      (.inl h) (.inr (scheduledPastAnchor role n a j ha b)) =
      finalCopyParity t - finalCopyParity t' := by
  change copyScheduleGraph initialCompleteGraph pivot (n + 1)
      h.val (copyScheduleAnchor (n + 1) j b a) -
    copyScheduleGraph initialCompleteGraph pivot (n + 1)
      (e.symm h).val (copyScheduleAnchor (n + 1) j b a) = _
  rw [hh, hh', copyScheduleGraph_path_to_anchor, copyScheduleGraph_path_to_anchor]
  · exact fun k hk => initialCompleteGraph_of_ne (hi'p k hk)
  · exact initialCompleteGraph_of_ne hi'a
  · exact j.isLt
  · exact fun k hk => initialCompleteGraph_of_ne (hip k hk)
  · exact initialCompleteGraph_of_ne hia
  · exact j.isLt

/-- A changed code with unchanged final parity supplies a genuine signed
square in the actual matching graph. All other graph entries remain arbitrary. -/
theorem scheduledMatchedGraph_changed_code {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role (n + 1)))
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (i i' : I) (hi : role i = .word) (hi' : role i' = .word)
    (t t' : Fin (n + 1) → Bool) (h : CopyScheduleH role (n + 1))
    (hh : h.val = copySchedulePath (n + 1) t i)
    (hh' : (e.symm h).val = copySchedulePath (n + 1) t' i')
    (hparity : finalCopyParity t = finalCopyParity t')
    (hcode : finiteAnchorCode (fun _ => 1) t ≠ finiteAnchorCode (fun _ => 1) t') :
    ∃ (j : Fin (n + 1)) (b : Bool),
      let a := scheduledPastAnchor role n (anchor j) j (ha j) b
      let G := scheduledMatchedGraph role pivot (n + 1) e
      (G (.inr a) (.inl h) = 2 ∨ G (.inr a) (.inl h) = -2) ∧
        G (.inl h) (.inr a) = 0 := by
  obtain ⟨j, b, hj⟩ := distinct_anchor_code_entry (fun _ => 1) t t' hcode
  have hs (u : Fin (n + 1) → Bool) : finalCopyParity u = 1 ∨ finalCopyParity u = -1 :=
    copyPathParity_sign (finiteCopyPath u) (n + 1)
  have hsign (u : Fin (n + 1) → Bool) :
      anchorCodeEntry (fun _ => 1) u j b = 1 ∨
        anchorCodeEntry (fun _ => 1) u j b = -1 :=
    anchorCodeEntry_sign (fun _ => 1) (fun _ => Or.inl rfl) u j b
  have hf : anchorIncoming (fun _ => 1) t j b - anchorIncoming (fun _ => 1) t' j b = 2 ∨
      anchorIncoming (fun _ => 1) t j b - anchorIncoming (fun _ => 1) t' j b = -2 := by
    rcases changed_anchor_code_one_sided _ _ _ _ (hs t) (hs t')
      (hsign t) (hsign t') hj with hx | hx
    · exact hx.1
    · have hz : finalCopyParity t - finalCopyParity t' = 0 := sub_eq_zero.mpr hparity
      rcases hx.2 with hx | hx <;> omega
  have hap : ∀ k < n + 1, anchor j ≠ pivot k := by
    intro k hk he
    have he' := congrArg role he
    rw [ha j, hp k hk] at he'
    cases he'
  have hai : anchor j ≠ i := by
    intro he
    have he' := congrArg role he
    rw [ha j, hi] at he'
    cases he'
  have hai' : anchor j ≠ i' := by
    intro he
    have he' := congrArg role he
    rw [ha j, hi'] at he'
    cases he'
  have hip : ∀ k < n + 1, i ≠ pivot k := by
    intro k hk he
    have he' := congrArg role he
    rw [hi, hp k hk] at he'
    cases he'
  have hi'p : ∀ k < n + 1, i' ≠ pivot k := by
    intro k hk he
    have he' := congrArg role he
    rw [hi', hp k hk] at he'
    cases he'
  refine ⟨j, b, ?_⟩
  dsimp only
  rw [scheduledMatchedGraph_anchor_word role pivot n e (anchor j) i i' j (ha j) b
    hap hai hai' t t' h hh hh',
    scheduledMatchedGraph_word_anchor role pivot n e (anchor j) i i' j (ha j) b
      hip hi'p hai.symm hai'.symm t t' h hh hh']
  exact ⟨hf, sub_eq_zero.mpr hparity⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFullMatchingGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained anchor interaction inside the full surviving-prime graph -/

namespace Ostmann
open scoped Classical

theorem scheduledHMatching_active {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) (h : CopyScheduleH role n) :
    scheduledHMatching role n e ⟨h.val, h.property.1⟩ = ⟨(e h).val, (e h).property.1⟩ := by
  exact Equiv.Perm.subtypeCongr.left_apply_subtype
    ((scheduleHSurvivorEquiv role n).permCongr e) (Equiv.refl _)
    (scheduleHSurvivorEquiv role n h)

theorem scheduledHMatching_inactive {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) (q : CopyScheduleAtoms role n)
    (hq : (copyScheduleRole role n q.val).copiedAt n ≠ true) :
    scheduledHMatching role n e q = q := by
  unfold scheduledHMatching
  simp only [Equiv.Perm.subtypeCongr.apply, dite_eq_right hq, Equiv.refl_apply]

theorem scheduledHMatching_retained {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) (z : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    scheduledHMatching role n e (scheduledRetainedEmbedding role n z) =
      scheduledRetainedEmbedding role n (Equiv.sumCongr e (Equiv.refl _) z) := by
  cases z with
  | inl h => exact scheduledHMatching_active role n e h
  | inr y =>
    apply scheduledHMatching_inactive
    change (copyScheduleRole role n y.val).copiedAt n ≠ true
    rw [y.property.2.1]
    decide

theorem scheduledHMatching_symm_retained {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) (z : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    (scheduledHMatching role n e).symm (scheduledRetainedEmbedding role n z) =
      scheduledRetainedEmbedding role n ((Equiv.sumCongr e (Equiv.refl _)).symm z) := by
  apply (scheduledHMatching role n e).injective
  rw [Equiv.apply_symm_apply, scheduledHMatching_retained, Equiv.apply_symm_apply]

theorem scheduledHMatching_graph {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (e : Equiv.Perm (CopyScheduleH role n))
    (z w : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    graphDifference (scheduledSurvivorGraph role pivot n)
      (transportGraph (scheduledHMatching role n e) (scheduledSurvivorGraph role pivot n))
      (scheduledRetainedEmbedding role n z) (scheduledRetainedEmbedding role n w) =
        scheduledMatchedGraph role pivot n e z w := by
  have hb (u v : CopyScheduleH role n ⊕ CopyScheduleY role n) :
      scheduledSurvivorGraph role pivot n (scheduledRetainedEmbedding role n u)
        (scheduledRetainedEmbedding role n v) =
      retainedInternalGraph (scheduledRetainedGraph role initialCompleteGraph pivot n) u v := by
    cases u <;> cases v <;> rfl
  change scheduledSurvivorGraph role pivot n (scheduledRetainedEmbedding role n z)
      (scheduledRetainedEmbedding role n w) -
    scheduledSurvivorGraph role pivot n
      ((scheduledHMatching role n e).symm (scheduledRetainedEmbedding role n z))
      ((scheduledHMatching role n e).symm (scheduledRetainedEmbedding role n w)) = _
  rw [scheduledHMatching_symm_retained, scheduledHMatching_symm_retained, hb, hb]
  rfl

theorem scheduledHMatching_symm {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH role n)) :
    (scheduledHMatching role n e).symm = scheduledHMatching role n e.symm := rfl

theorem scheduledHMatching_trans {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (e f : Equiv.Perm (CopyScheduleH role n)) :
    (scheduledHMatching role n e).trans (scheduledHMatching role n f) =
      scheduledHMatching role n (e.trans f) := by
  unfold scheduledHMatching
  rw [Equiv.Perm.subtypeCongr.trans, Equiv.permCongr_trans]
  rfl

theorem paritySlotPerm_inv {n m : ℕ} (e : FinalParityReassignments n m) :
    paritySlotPerm (e⁻¹) = (paritySlotPerm e).symm := by
  apply Equiv.ext
  rintro ⟨path, i⟩
  cases path <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPriorMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic mass floors for every original signed character marginal -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem harmonic_mass_inv_le_exp (Q : Finset ℕ) (C L : ℝ)
    (hQ : Real.exp (-C * L) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹) :
    (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (C * L) := by
  have h := inv_anti₀ (Real.exp_pos (-C * L)) hQ
  simpa only [← Real.exp_neg, neg_mul, neg_neg] using h

theorem harmonic_mass_inv_energy_budget (Q : Finset ℕ) (C L M : ℝ)
    (hC : 0 ≤ C) (hLM : L ≤ M)
    (hQ : Real.exp (-C * L) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹) :
    (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (C * (1 + M)) := by
  apply (harmonic_mass_inv_le_exp Q C L hQ).trans
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hC)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RoundedEnergyCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical cutoffs for the actual square-root-reserve schedule -/

namespace Ostmann
open Filter

/-- The signed root-frequency set includes zero and both endpoints. -/
theorem card_transferFrequencyRange (V : ℕ) : (transferFrequencyRange V).card = 2 * V + 1 := by
  simp only [transferFrequencyRange, Int.card_Icc]
  omega

/-- At fixed depth the whole rounded frequency family has an exponential
bound linear in the word length, with its square-root reserve absorbed. -/
theorem eventual_rounded_frequency_card (n : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    ∀ᶠ m : ℝ in atTop, ∀ j ≤ n,
      ((transferFrequencyRange (naturalTransferCutoff (d * m) m j)).card : ℝ) ≤
        Real.exp (((2 : ℝ) ^ n * d + 1) * m) := by
  obtain ⟨M, hM⟩ := sqrt_cost_sublinear (2 * (4 : ℝ) ^ n) (Real.log 3) 1
    (by positivity) (by norm_num)
  filter_upwards [eventually_ge_atTop M, eventually_ge_atTop (0 : ℝ)] with m hm hm0 j hj
  have hb := hM m hm
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
  have h4 : (4 : ℝ) ^ j ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hj
  have he : 0 ≤ transferErrorScale (d * m) m j := by unfold transferErrorScale; positivity
  have hfloor : (naturalTransferCutoff (d * m) m j : ℝ) ≤
      Real.exp (transferErrorScale (d * m) m j) := Nat.floor_le (Real.exp_pos _).le
  have hone : 1 ≤ Real.exp (transferErrorScale (d * m) m j) := Real.one_le_exp he
  rw [card_transferFrequencyRange]
  push_cast
  calc
    _ ≤ 3 * Real.exp (transferErrorScale (d * m) m j) := by linarith
    _ = Real.exp (Real.log 3 + transferErrorScale (d * m) m j) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold transferErrorScale
      have ha := mul_le_mul_of_nonneg_right h2 (mul_nonneg hd hm0)
      have hc := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg m)
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentUniqueRootEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique histories remove multiplicity from the actual final energy -/

namespace Ostmann
open scoped BigOperators Classical

section
variable {I D R : Type*} [Fintype I] [Fintype D] [Fintype R]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)

include hP in
theorem constituentPrimeTerm_nonzero_valid (t : FrequencyTree ℤ n)
    (q : SurvivingConstituent role size n → P)
    (h : constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound ranges
      leaf center t q ≠ 0) :
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod⟩ t := by
  have hw := (mul_ne_zero_iff.mp h).1
  exact (fullAtomTransferWeight_support role childBound pivotBound ranges leaf n _ t hw).2

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledRootIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The root frequency as an element of its actual finite cutoff range -/

namespace Ostmann

theorem scheduledRootIndex_eq_iff (V : ℕ → ℕ) (n : ℕ) (d d' : ScheduledFrequencyIndex V n) :
    scheduledRootIndex V n d = scheduledRootIndex V n d' ↔
      frequencyRoot n (scheduledFrequencyHistory V n d) =
        frequencyRoot n (scheduledFrequencyHistory V n d') := Subtype.ext_iff

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPairComplexity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete word and support counts for the actual two histories -/

namespace Ostmann
open scoped Classical

theorem WordTransferTemplate.wordsBounded_mono {V : Type*} {n B C : ℕ}
    (T : WordTransferTemplate V n) (hT : T.WordsBounded B) (hBC : B ≤ C) : T.WordsBounded C := by
  induction T with
  | leaf w => exact hT.trans hBC
  | node d L R ihL ihR => exact ⟨hT.1.trans hBC, ihL hT.2.1, ihR hT.2.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRootRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adding one exact product cutoff at the root of a history -/

namespace Ostmann

open scoped BigOperators Classical

theorem WordRangeDecoration.prependRoot_count {σ : Type*} {n : ℕ}
    (r : WordRange σ) (D : WordRangeDecoration σ n) :
    (D.prependRoot r).count = D.count + 1 := by
  cases D with
  | leaf ranges => simp only [prependRoot, count, List.length_cons]
  | node ranges L R => simp only [prependRoot, count, List.length_cons]; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentRangeCounts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counts for the actual ranges, including the reciprocal-product cutoff -/

namespace Ostmann
open scoped Classical

/-- The added root cutoff costs one test; all inherited tests are counted
on their actual binary history tree. -/
theorem expandedRootRanges_count_le {I σ : Type*}
    (role : I → CopyScheduleRole) (n K : ℕ)
    (words : CopyScheduleAtoms role n → List σ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hK : ∀ j ≤ n, (ranges j).length ≤ K) :
    (expandedRootRanges role n words ranges).count ≤ K * (2 ^ (n + 1) - 1) := by
  exact WordRangeDecoration.count_le _ K
    (expandedScheduleRanges_count_bounded role _ ranges n K hK [] _)

theorem expandedRootRanges_cutoff_count_le {I σ : Type*}
    (role : I → CopyScheduleRole) (n K : ℕ)
    (words : CopyScheduleAtoms role n → List σ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hK : ∀ j ≤ n, (ranges j).length ≤ K)
    (r : WordRange (ExpandedScheduledVariable σ n)) :
    ((expandedRootRanges role n words ranges).prependRoot r).count ≤
      K * (2 ^ (n + 1) - 1) + 1 := by
  rw [WordRangeDecoration.prependRoot_count]
  exact Nat.add_le_add_right (expandedRootRanges_count_le role n K words ranges hK) 1

/-- Both histories, with the extra cutoff on the left, share one constant
range-count bound and hence the linear bound used in the numerical estimate. -/
theorem expandedRootRanges_pair_linear_count {I σ : Type*}
    (role : I → CopyScheduleRole) (n K : ℕ)
    (words words' : CopyScheduleAtoms role n → List σ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (hK : ∀ j ≤ n, (ranges j).length ≤ K)
    (r : WordRange (ExpandedScheduledVariable σ n)) (m : ℝ) (hm : 0 ≤ m) :
    (((expandedRootRanges role n words ranges).prependRoot r).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) * (1 + m) ∧
    ((expandedRootRanges role n words' ranges).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) * (1 + m) := by
  have hL : (((expandedRootRanges role n words ranges).prependRoot r).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) := by
    exact_mod_cast expandedRootRanges_cutoff_count_le role n K words ranges hK r
  have hR : ((expandedRootRanges role n words' ranges).count : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) := by
    exact_mod_cast (expandedRootRanges_count_le role n K words' ranges hK).trans (Nat.le_add_right _ 1)
  have hb : ((K * (2 ^ (n + 1) - 1) + 1 : ℕ) : ℝ) ≤
      (K * (2 ^ (n + 1) - 1) + 1 : ℕ) * (1 + m) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
  exact ⟨hL.trans hb, hR.trans hb⟩

/-- With linear atom sizes, the concrete word budget stays linear. -/
theorem constituent_word_budget_linear {I : Type*} [Fintype I]
    (n A S : ℕ) (s m : ℝ) (hs : (S : ℝ) ≤ s * (1 + m)) (hm : 0 ≤ m) :
    ((2 * 3 ^ n * Fintype.card I * S + A * S + 4 : ℕ) : ℝ) ≤
      (((2 * 3 ^ n * Fintype.card I + A : ℕ) : ℝ) * s + 4) * (1 + m) := by
  have hmult := mul_le_mul_of_nonneg_left hs
    (Nat.cast_nonneg (2 * 3 ^ n * Fintype.card I + A))
  push_cast at hmult ⊢
  nlinarith only [hm, hmult]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentFinalComplexity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word and prime counts for the actual final constituent pair -/
namespace Ostmann
open scoped Classical

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (e : Equiv.Perm (SurvivingConstituent role size n))
local notation "W" => primeWordEmbedding (scheduleConstituentWord role size n)
local notation "Wp" => primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))

theorem constituent_final_word_bounds
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (S A : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S)
    (hA : ∀ j ≤ n, ∀ r ∈ ranges j, r.atoms.length ≤ A) :
    let B := 2 * 3 ^ n * Fintype.card I * S + A * S + 4
    (expandedRootTemplate role n W childBound pivotBound).WordsBounded B ∧
    (expandedRootTemplate role n Wp childBound pivotBound).WordsBounded B ∧
    (expandedRootRanges role n W ranges).WordsBounded B ∧
    (expandedRootRanges role n Wp ranges).WordsBounded B ∧
    (expandedRootRanges role n W (totalAtomUnitRanges role)).WordsBounded B ∧
    (expandedRootRanges role n Wp (totalAtomUnitRanges role)).WordsBounded B := by
  dsimp only
  have hw (i) : (W i).length ≤ S := by
    simp only [primeWordEmbedding, List.length_map, scheduleConstituentWord_length]
    exact hsize _
  have hw' (i) : (Wp i).length ≤ S := by
    simpa only [primeWordEmbedding, List.length_map] using hw i
  have ht : 2 * 3 ^ n * Fintype.card I * S + 4 ≤
      2 * 3 ^ n * Fintype.card I * S + A * S + 4 := by omega
  have hr : A * S + 1 ≤ 2 * 3 ^ n * Fintype.card I * S + A * S + 4 := by omega
  have hd (words : CopyScheduleAtoms role n → List (Option (SurvivingConstituent role size n)))
      (hwords : ∀ i, (words i).length ≤ S) :
      (expandedRootRanges role n words ranges).WordsBounded
        (2 * 3 ^ n * Fintype.card I * S + A * S + 4) := by
    apply WordRangeDecoration.wordsBounded_mono _ _ hr
    exact expandedScheduleRanges_words_bounded role _ ranges n A S hS hA [] _
      (fun i => by simpa only [List.length_map] using hwords i)
  exact ⟨WordTransferTemplate.wordsBounded_mono _
      (expandedRootTemplate_size role n W childBound pivotBound S hS hw) ht,
    WordTransferTemplate.wordsBounded_mono _
      (expandedRootTemplate_size role n Wp childBound pivotBound S hS hw') ht,
    hd W hw, hd Wp hw',
    WordRangeDecoration.wordsBounded_mono _ (totalAtomUnits_words_bounded role n W S hS hw) ht,
    WordRangeDecoration.wordsBounded_mono _ (totalAtomUnits_words_bounded role n Wp S hS hw') ht⟩

theorem constituent_final_prime_count (S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S) :
    (expandedSchedulePrimes role n n [] (fun i => (W i).map Sum.inl)).count +
    (expandedSchedulePrimes role n n [] (fun i => (Wp i).map Sum.inl)).count ≤
      2 * ((3 ^ n * Fintype.card I * S) * (2 ^ n - 1)) := by
  have hw (i) : (W i).length ≤ S := by
    simp only [primeWordEmbedding, List.length_map, scheduleConstituentWord_length]
    exact hsize _
  have hw' (i) : (Wp i).length ≤ S := by
    simpa only [primeWordEmbedding, List.length_map] using hw i
  have hL := expandedRootPrimes_count role n S hS W hw
  have hR := expandedRootPrimes_count role n S hS Wp hw'
  omega

theorem constituent_final_top_count (S : ℕ) (hsize : ∀ i, size i ≤ S) :
    (constituentPrimePairChecks (SurvivingConstituent role size n) ++
      atomPairChecks W ++ atomPairChecks Wp).length ≤
        3 * (3 ^ n * Fintype.card I * S) ^ 2 := by
  have hw (i) : (W i).length ≤ S := by
    simp only [primeWordEmbedding, List.length_map, scheduleConstituentWord_length]
    exact hsize _
  have hw' (i) : (Wp i).length ≤ S := by
    simpa only [primeWordEmbedding, List.length_map] using hw i
  have hcard : Fintype.card (Σ i, Fin (size i)) ≤ Fintype.card I * S := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (f := size) (g := fun _ => S)
        (fun i _ => hsize i))
  have hK : Fintype.card (SurvivingConstituent role size n) ≤
      3 ^ n * Fintype.card I * S := by
    have hh := copyScheduleAtoms_card_le (fun i : Σ a, Fin (size a) => role i.1) n
    exact hh.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left (3 ^ n) hcard)
  have hchecks := atomPairChecks_length (fun i : SurvivingConstituent role size n => [some i])
    1 (by intro i; rfl)
  simp only [Nat.mul_one] at hchecks
  have hL := atomPairChecks_length W S hw
  have hR := atomPairChecks_length Wp S hw'
  have ha := Nat.pow_le_pow_left hK 2
  have hb := Nat.pow_le_pow_left
    (Nat.mul_le_mul_right S (copyScheduleAtoms_card_le role n)) 2
  simp only [List.length_append, constituentPrimePairChecks]
  omega

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentFinalCostData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual final pair counts at the linear constituent-size scale -/
namespace Ostmann
open scoped Classical

theorem constituentFinalCountRate_nonneg (N n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ constituentFinalCountRate N n s := by
  unfold constituentFinalCountRate
  positivity

theorem constituent_final_linear_counts {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (SurvivingConstituent role size n))
    (S : ℕ) (s m : ℝ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S)
    (hs : 0 ≤ s) (hm : 0 ≤ m) (hSm : (S : ℝ) ≤ s * (1 + m)) :
    let W := primeWordEmbedding (scheduleConstituentWord role size n)
    let W' := primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))
    let a := constituentFinalCountRate (Fintype.card I) n s
    (((expandedSchedulePrimes role n n [] (fun i => (W i).map Sum.inl)).count +
      (expandedSchedulePrimes role n n [] (fun i => (W' i).map Sum.inl)).count : ℕ) : ℝ) ≤
        a * (1 + m) ∧
    ((constituentPrimePairChecks (SurvivingConstituent role size n) ++
      atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤ a * (1 + m) ^ 2 := by
  intro W W' a
  have hp := constituent_final_prime_count role size n e S hS hsize
  have hc := constituent_final_top_count role size n e S hsize
  have hrealp : (((expandedSchedulePrimes role n n [] (fun i => (W i).map Sum.inl)).count +
      (expandedSchedulePrimes role n n [] (fun i => (W' i).map Sum.inl)).count : ℕ) : ℝ) ≤
      2 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * S * (2 ^ n - 1 : ℕ) := by
    calc
      _ ≤ 2 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * S * (2 ^ n - 1 : ℕ)) := by
        exact_mod_cast hp
      _ = _ := by ring
  have hrealc : ((constituentPrimePairChecks (SurvivingConstituent role size n) ++
      atomPairChecks W ++ atomPairChecks W').length : ℝ) ≤
      3 * ((((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * S) ^ 2 := by
    exact_mod_cast hc
  have ha1 : 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ) ≤ a := by
    dsimp [a, constituentFinalCountRate]
    linarith [sq_nonneg ((((3 ^ n * Fintype.card I : ℕ) : ℝ) : ℝ) * s)]
  have ha2 : 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * s) ^ 2 ≤ a := by
    dsimp [a, constituentFinalCountRate]
    have hh : 0 ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ) := by positivity
    linarith
  constructor
  · calc
      _ ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * S * (2 ^ n - 1 : ℕ) := hrealp
      _ ≤ 2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * (s * (1 + m)) * (2 ^ n - 1 : ℕ) := by gcongr
      _ = (2 * ((3 ^ n * Fintype.card I : ℕ) : ℝ) * s * (2 ^ n - 1 : ℕ)) * (1 + m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha1 (by linarith)
  · calc
      _ ≤ 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * S) ^ 2 := hrealc
      _ ≤ 3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * (s * (1 + m))) ^ 2 := by gcongr
      _ = (3 * (((3 ^ n * Fintype.card I : ℕ) : ℝ) * s) ^ 2) * (1 + m) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledHistoryError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both actual history sums preserve double-exponential cancellation -/

namespace Ostmann
open Filter

theorem eventual_scheduled_history_error (n : ℕ) (C H z α c : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hz : 0 ≤ z) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℝ) (V : ℕ → ℕ), Monotone V →
      0 ≤ m → m ≤ z * L →
      ((transferFrequencyRange (V n)).card : ℝ) ≤ Real.exp (C * m) →
      (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 *
        Real.exp (-c * Real.exp (α * L)) ≤ Real.exp (-H * (2 ^ n : ℕ) * m) := by
  let A : ℝ := ((2 * (2 ^ (n + 1) - 1) : ℕ) : ℝ) * C
  have hA : 0 ≤ A := mul_nonneg (by positivity) hC
  have htotal : 0 ≤ A + H * (2 ^ n : ℕ) := by positivity
  filter_upwards [eventual_polynomial_log_budget (A + H * (2 ^ n : ℕ)) z α c 1
    htotal hz hα hc] with L hL
  intro m V hV hm hmL hS
  have hpoly := hL m hm hmL
  simp only [pow_one] at hpoly
  have hcard := scheduledFrequencyIndex_pair_card_bound V hV n C m hS
  have hcard' : (Fintype.card (ScheduledFrequencyIndex V n) : ℝ) ^ 2 ≤ Real.exp (A * m) := by
    simpa only [A, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcard
  calc
    _ ≤ Real.exp (A * m) * Real.exp (-c * Real.exp (α * L)) :=
      mul_le_mul_of_nonneg_right hcard' (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPrimeFrequencySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every live final term has nonzero frequencies, including at its leaves -/
namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem constituentPrimeTerm_nonzero_frequencies {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hXlo : 1 < X * lo)
    (center : ∀ p : ℕ, ZMod p) (t : FrequencyTree ℤ n)
    (q : SurvivingConstituent role size n → P)
    (hq : constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) center t q ≠ 0) :
    NonzeroInternalFrequencies n t ∧ ∀ a ∈ allFrequencyList n t, a ≠ 0 := by
  have hv := constituentPrimeTerm_nonzero_valid role size χ κ pivot n P hP childBound
    pivotBound ranges (scheduleFourierLeaf role ψ X lo hi) center t q hq
  refine ⟨hv.nonzero_internal _ _ _ _, ?_⟩
  have hw := (mul_ne_zero_iff.mp hq).1
  exact fullAtomFourierWeight_all_frequencies_ne_zero role childBound pivotBound ranges
    ψ X lo hi hX hXlo n _ t hw

theorem finite_frequency_range_data (P : Finset ℕ) (hP : P.Nonempty) (R : ℝ) (V : ℕ)
    (hlarge : ∀ p ∈ P, V < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ R)
    (n : ℕ) (t : FrequencyTree ℤ n)
    (hz : ∀ a ∈ allFrequencyList n t, a ≠ 0)
    (hfreq : ∀ a ∈ allFrequencyList n t, a.natAbs ≤ V) :
    (∀ p ∈ P, ∀ a ∈ allFrequencyList n t, 0 < a.natAbs ∧ a.natAbs < p) ∧
      ∀ a ∈ allFrequencyList n t, |(a : ℝ)| ≤ R := by
  constructor
  · intro p hp a ha
    exact ⟨Int.natAbs_pos.mpr (hz a ha), (hfreq a ha).trans_lt (hlarge p hp)⟩
  · intro a ha
    obtain ⟨p, hp⟩ := hP
    have hh : (a.natAbs : ℝ) ≤ R :=
      (Nat.cast_le.mpr (hfreq a ha)).trans ((Nat.cast_le.mpr (hlarge p hp).le).trans (hupper p hp))
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPeriodBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial exponential bound for the actual common frequency period -/

namespace Ostmann

theorem wordTransferFullPeriod_le_exp (n : ℕ) (t : FrequencyTree ℤ n) (B V : ℕ)
    (b C m : ℝ) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hB : (B : ℝ) ≤ b * (1 + m)) (hV : (V : ℝ) ≤ Real.exp (C * (1 + m)))
    (hf : ∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) :
    (wordTransferFullPeriod n t B : ℝ) ≤
      Real.exp (C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) := by
  let e := (2 ^ n - 1) * (B ^ (n + 1) + 1) + (2 ^ (n + 1) - 1)
  have hr : 0 ≤ 1 + m := by linarith
  have hr1 : 1 ≤ (1 + m) ^ (n + 1) := one_le_pow₀ (by linarith)
  have hbp : (B : ℝ) ^ (n + 1) ≤ b ^ (n + 1) * (1 + m) ^ (n + 1) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg B) hB (n + 1)
  have he : (e : ℝ) ≤ wordPeriodExponent n b * (1 + m) ^ (n + 1) := by
    dsimp [e, wordPeriodExponent]
    push_cast
    calc
      _ ≤ ((2 ^ n - 1 : ℕ) : ℝ) * ((b ^ (n + 1) + 1) * (1 + m) ^ (n + 1)) +
          ((2 ^ (n + 1) - 1 : ℕ) : ℝ) * (1 + m) ^ (n + 1) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (by nlinarith only [hbp, hr1]) (Nat.cast_nonneg _))
          (le_mul_of_one_le_right (Nat.cast_nonneg _) hr1)
      _ = _ := by ring
  have hnat : (wordTransferFullPeriod n t B : ℝ) ≤ (V : ℝ) ^ e := by
    exact_mod_cast wordTransferFullPeriod_le n t B V hf
  calc
    _ ≤ (V : ℝ) ^ e := hnat
    _ ≤ (Real.exp (C * (1 + m))) ^ e :=
      pow_le_pow_left₀ (Nat.cast_nonneg V) hV e
    _ = Real.exp ((e : ℝ) * (C * (1 + m))) := (Real.exp_nat_mul _ e).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hC hr)
      calc
        _ = (C * (1 + m)) * e := by ring
        _ ≤ (C * (1 + m)) * (wordPeriodExponent n b * (1 + m) ^ (n + 1)) := hh
        _ = _ := by rw [pow_succ]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalPairPeriodScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The final history pair's actual modulus fits below the long-prime scale -/
namespace Ostmann
open Filter

theorem eventual_final_pair_period_scale (n : ℕ) (b C z β : ℝ)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hz : 0 ≤ z) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℝ) (B V A : ℕ) (t t' : FrequencyTree ℤ n),
      0 ≤ m → m ≤ z * L → (B : ℝ) ≤ b * (1 + m) →
      (V : ℝ) ≤ Real.exp (C * (1 + m)) →
      (∀ s ∈ allFrequencyList n t, s.natAbs ≤ V) →
      (∀ s ∈ allFrequencyList n t', s.natAbs ≤ V) →
      Real.exp (Real.exp (β * L)) ≤ (A : ℝ) →
      wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A := by
  have hK : 0 ≤ 2 * C * wordPeriodExponent n b := by
    unfold wordPeriodExponent
    positivity
  filter_upwards [eventual_polynomial_log_budget (2 * C * wordPeriodExponent n b)
    z β 1 (n + 2) hK hz hβ zero_lt_one] with L hL m B V A t t' hm hmL hB hV hf hf' hA
  have hleft := wordTransferFullPeriod_le_exp n t B V b C m hC hm hB hV hf
  have hright := wordTransferFullPeriod_le_exp n t' B V b C m hC hm hB hV hf'
  have hprod : ((wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B : ℕ) : ℝ) ≤
      Real.exp (2 * C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) := by
    push_cast
    calc
      _ ≤ Real.exp (C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) *
          Real.exp (C * wordPeriodExponent n b * (1 + m) ^ (n + 2)) :=
        mul_le_mul hleft hright (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he := hL m hm hmL
  simp only [one_mul] at he
  exact_mod_cast hprod.trans ((Real.exp_le_exp.mpr he).trans hA)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalFactorialBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factorial gain from the actual final reassignment family -/

namespace Ostmann

open scoped BigOperators

theorem final_reassignment_card_exp_lower (n m : ℕ) :
    Real.exp ((2 ^ (n + 1) : ℝ) * m * ((n : ℝ) * Real.log 2 - 1)) ≤
      (Fintype.card (FinalParityReassignments n m) : ℝ) := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  have h := pow_le_pow_left₀ (Real.exp_nonneg _) (factorial_exp_lower hq) (2 * m)
  rw [← Real.exp_nat_mul] at h
  rw [card_finalParityReassignments]
  push_cast
  rw [← pow_mul]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  rw [Real.log_pow, pow_succ]
  ring

/-- At fixed depth, the diagonal exponential cost is beaten by the
factorial family as soon as its entropy margin is positive. -/
theorem final_diagonal_entropy_bound (n m : ℕ) (a C : ℝ)
    (ha : a ≤ (n : ℝ) * Real.log 2 - 1 - C) :
    Real.exp (C * (2 ^ (n + 1) : ℝ) * m) /
        (Fintype.card (FinalParityReassignments n m) : ℝ) ≤
      Real.exp (-a * (2 ^ (n + 1) : ℝ) * m) := by
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := FinalParityReassignments n m))).mpr
  calc
    _ ≤ Real.exp (-a * (2 ^ (n + 1) : ℝ) * m) *
        Real.exp ((2 ^ (n + 1) : ℝ) * m * ((n : ℝ) * Real.log 2 - 1)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ht : 0 ≤ (2 ^ (n + 1) : ℝ) * m := by positivity
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (final_reassignment_card_exp_lower n m) (Real.exp_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalExponentialContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative contradiction at the final permutation stage -/

namespace Ostmann

theorem final_exponential_contradiction (n m : ℕ) (B₁ D C δ T B E : ℝ) (η : ℂ)
    (hT : T ≤ Real.exp (D * (2 ^ (n + 1) : ℝ) * m))
    (hB0 : 0 ≤ B) (hE0 : 0 ≤ E)
    (hB : B ≤ Real.exp (C * (2 ^ (n + 1) : ℝ) * m))
    (hE : E ≤ Real.exp (-(D + 2 * B₁ + δ) * (2 ^ (n + 1) : ℝ) * m))
    (hentropy : C + D + 2 * B₁ + δ ≤ (n : ℝ) * Real.log 2 - 1)
    (hmargin : Real.log 2 < δ * (2 ^ (n + 1) : ℝ) * m)
    (hlower : Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤ ‖η‖)
    (hcompare : ‖η‖ ^ 2 ≤ T *
      (B / (Fintype.card (FinalParityReassignments n m) : ℝ) + E)) : False := by
  let s : ℝ := (2 ^ (n + 1) : ℝ) * m
  have hcard : 0 < (Fintype.card (FinalParityReassignments n m) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := FinalParityReassignments n m)
  have hdiag : B / (Fintype.card (FinalParityReassignments n m) : ℝ) ≤
      Real.exp (-(D + 2 * B₁ + δ) * s) := by
    apply (div_le_div_of_nonneg_right hB hcard.le).trans
    simpa only [s, mul_assoc] using
      final_diagonal_entropy_bound n m (D + 2 * B₁ + δ) C (by linarith)
  have hsum : B / (Fintype.card (FinalParityReassignments n m) : ℝ) + E ≤
      2 * Real.exp (-(D + 2 * B₁ + δ) * s) := by
    have he : E ≤ Real.exp (-(D + 2 * B₁ + δ) * s) := by
      simpa only [s, mul_assoc] using hE
    linarith
  have hu : ‖η‖ ^ 2 ≤ 2 * Real.exp (-(2 * B₁ + δ) * s) := by
    apply hcompare.trans
    calc
      _ ≤ Real.exp (D * s) * (2 * Real.exp (-(D + 2 * B₁ + δ) * s)) := by
        apply mul_le_mul (by simpa only [s, mul_assoc] using hT) hsum
          (add_nonneg (div_nonneg hB0 hcard.le) hE0) (Real.exp_nonneg _)
      _ = _ := by rw [show Real.exp (D * s) * (2 * Real.exp (-(D + 2 * B₁ + δ) * s)) =
          2 * (Real.exp (D * s) * Real.exp (-(D + 2 * B₁ + δ) * s)) by ring,
          ← Real.exp_add]; congr 2; ring
  have hl : Real.exp (-(2 * B₁) * s) ≤ ‖η‖ ^ 2 := by
    have hl' : Real.exp (-B₁ * s) ≤ ‖η‖ := by simpa only [s, mul_assoc] using hlower
    have h := pow_le_pow_left₀ (Real.exp_nonneg _) hl' 2
    rw [← Real.exp_nat_mul] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hstrict : 2 * Real.exp (-(2 * B₁ + δ) * s) < Real.exp (-(2 * B₁) * s) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
    apply Real.exp_lt_exp.mpr
    have hm' : Real.log 2 < δ * s := by simpa only [s, mul_assoc] using hmargin
    nlinarith
  exact (not_lt_of_ge (hl.trans hu)) hstrict

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFinalContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The canonical history sum is negligible in the final factorial comparison -/
namespace Ostmann
open Filter

theorem eventual_scheduled_final_contradiction (n : ℕ) (B₁ D C δ z α c : ℝ)
    (hB₁ : 0 ≤ B₁) (hD : 0 ≤ D) (hδ : 0 < δ) (hz : 0 ≤ z)
    (hα : 0 < α) (hc : 0 < c)
    (hentropy : C + D + 2 * B₁ + δ ≤ (n : ℝ) * Real.log 2 - 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ) (V : ℕ → ℕ) (η : ℂ),
      Monotone V → (m : ℝ) ≤ z * L →
      ((transferFrequencyRange (V (n + 1))).card : ℝ) ≤
        Real.exp (D * (2 ^ (n + 1) : ℝ) * m) →
      Real.log 2 < δ * (2 ^ (n + 1) : ℝ) * m →
      Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤ ‖η‖ →
      ‖η‖ ^ 2 ≤ ((transferFrequencyRange (V (n + 1))).card : ℝ) *
        (Real.exp (C * (2 ^ (n + 1) : ℝ) * m) /
          (Fintype.card (FinalParityReassignments n m) : ℝ) +
        (Fintype.card (ScheduledFrequencyIndex V (n + 1)) : ℝ) ^ 2 *
          Real.exp (-c * Real.exp (α * L))) → False := by
  have hroot : 0 ≤ D * (2 ^ (n + 1) : ℝ) := by positivity
  have herror : 0 ≤ D + 2 * B₁ + δ := by positivity
  filter_upwards [eventual_scheduled_history_error (n + 1)
    (D * (2 ^ (n + 1) : ℝ)) (D + 2 * B₁ + δ) z α c hroot herror hz hα hc]
    with L hL m V η hV hm hcard hmargin hlower hcompare
  have herr := hL (m : ℝ) V hV (Nat.cast_nonneg m) hm (by simpa only [mul_assoc] using hcard)
  exact final_exponential_contradiction n m B₁ D C δ
    ((transferFrequencyRange (V (n + 1))).card : ℝ)
    (Real.exp (C * (2 ^ (n + 1) : ℝ) * m))
    ((Fintype.card (ScheduledFrequencyIndex V (n + 1)) : ℝ) ^ 2 *
      Real.exp (-c * Real.exp (α * L))) η hcard (Real.exp_nonneg _)
    (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)) le_rfl (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using herr) hentropy hmargin hlower hcompare

theorem selected_prime_energy_exponent_le (n m : ℕ) (L A ε : ℝ)
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hL : L ≤ (m : ℝ)) :
    A * (2 ^ (n + 1) : ℝ) * L + ε * m ≤
      (A + ε) * (2 ^ (n + 1) : ℝ) * m := by
  have hr : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hmain := mul_le_mul_of_nonneg_left hL (mul_nonneg hA (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1)))
  have hsmall := mul_le_mul_of_nonneg_left hr (mul_nonneg hε (Nat.cast_nonneg m))
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedFinalPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Final parity permutations fix every top slot

Only the explicitly selected bulk slots are permuted among paths of equal
parity. The remaining word slots, in particular the top labels, stay fixed.
-/
namespace Ostmann
open scoped Classical BigOperators

theorem selectedFinalPerm_bulk {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (x : ParityPathSum n × Fin m) :
    selectedFinalPerm role n m bulk hbulk e (selectedParityH role n m bulk hbulk x) =
      selectedParityH role n m bulk hbulk (paritySlotPerm e x) := by
  have hx : (selectedParityCoordinates role n m bulk hbulk x).val =
      selectedParityH role n m bulk hbulk x := rfl
  rw [← hx]
  unfold selectedFinalPerm
  rw [Equiv.Perm.subtypeCongr.left_apply_subtype]
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

theorem selectedFinalPerm_other {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1))
    (hh : h ∉ Set.range (selectedParityH role n m bulk hbulk)) :
    selectedFinalPerm role n m bulk hbulk e h = h := by
  unfold selectedFinalPerm
  simp only [Equiv.Perm.subtypeCongr.apply, dite_eq_right hh, Equiv.refl_apply]

theorem selectedFinalPerm_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1)) :
    copyScheduleOrigin (n + 1) (selectedFinalPerm role n m bulk hbulk e h).val =
      copyScheduleOrigin (n + 1) h.val := by
  by_cases hh : h ∈ Set.range (selectedParityH role n m bulk hbulk)
  · obtain ⟨x, rfl⟩ := hh
    rw [selectedFinalPerm_bulk]
    change copyScheduleOrigin (n + 1) (copySchedulePath (n + 1)
      (parityPathValue (paritySlotPerm e x).1) (bulk (paritySlotPerm e x).2)) =
      copyScheduleOrigin (n + 1) (copySchedulePath (n + 1) (parityPathValue x.1) (bulk x.2))
    simp only [copyScheduleOrigin_path, paritySlotPerm_preserves_position]
  · rw [selectedFinalPerm_other role n m bulk hbulk e h hh]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedFullFinalPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-bulk permutations on all actual surviving prime coordinates -/
namespace Ostmann
open scoped Classical BigOperators

theorem selectedFullFinalPerm_active {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1)) :
    selectedFullFinalPerm role n m bulk hbulk e ⟨h.val, h.property.1⟩ =
      ⟨(selectedFinalPerm role n m bulk hbulk e h).val,
        (selectedFinalPerm role n m bulk hbulk e h).property.1⟩ := by
  have hh := Equiv.Perm.subtypeCongr.left_apply_subtype
    ((scheduleHSurvivorEquiv role (n + 1)).permCongr
      (selectedFinalPerm role n m bulk hbulk e)) (Equiv.refl _)
    (scheduleHSurvivorEquiv role (n + 1) h)
  exact hh

theorem selectedFullFinalPerm_inactive {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (q : CopyScheduleAtoms role (n + 1))
    (hq : (copyScheduleRole role (n + 1) q.val).copiedAt (n + 1) ≠ true) :
    selectedFullFinalPerm role n m bulk hbulk e q = q := by
  unfold selectedFullFinalPerm
  simp only [Equiv.Perm.subtypeCongr.apply, dite_eq_right hq, Equiv.refl_apply]

theorem selectedFullFinalPerm_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (q : CopyScheduleAtoms role (n + 1)) :
    copyScheduleOrigin (n + 1) (selectedFullFinalPerm role n m bulk hbulk e q).val =
      copyScheduleOrigin (n + 1) q.val := by
  by_cases hq : (copyScheduleRole role (n + 1) q.val).copiedAt (n + 1) = true
  · have he := selectedFullFinalPerm_active role n m bulk hbulk e ⟨q.val, q.property, hq⟩
    rw [he]
    exact selectedFinalPerm_origin role n m bulk hbulk e _
  · rw [selectedFullFinalPerm_inactive role n m bulk hbulk e q hq]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedFinalInteraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A moved selected-bulk slot gives the final one-sided interaction -/
namespace Ostmann
open scoped Classical

theorem selected_final_pair_interaction {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (h : CopyScheduleH role (n + 1)) (j : Fin (n + 1)) (b : Bool) (i : Fin m),
      let a := scheduledPastAnchor role n (anchor j) j (ha j) b
      let G := scheduledMatchedGraph role pivot (n + 1) (selectedPairMatching role n m bulk hbulk e f)
      copyScheduleOrigin (n + 1) h.val = bulk i ∧
      (G (.inr a) (.inl h) = 2 ∨ G (.inr a) (.inl h) = -2) ∧
        G (.inl h) (.inr a) = 0 := by
  obtain ⟨x, hx⟩ := distinct_reassignments_change_code (fun _ => 1)
    (fun _ => Or.inl rfl) e f hef
  let h := selectedParityH role n m bulk hbulk (paritySlotPerm e x)
  have he : selectedFinalPerm role n m bulk hbulk e (selectedParityH role n m bulk hbulk x) = h :=
    selectedFinalPerm_bulk role n m bulk hbulk e x
  have hf : (selectedPairMatching role n m bulk hbulk e f).symm h =
      selectedParityH role n m bulk hbulk (paritySlotPerm f x) := by
    change selectedFinalPerm role n m bulk hbulk f ((selectedFinalPerm role n m bulk hbulk e).symm h) = _
    rw [← he, Equiv.symm_apply_apply]
    exact selectedFinalPerm_bulk role n m bulk hbulk f x
  have hpath : ((selectedPairMatching role n m bulk hbulk e f).symm h).val =
      copySchedulePath (n + 1) (parityPathValue (paritySlotPerm f x).1)
        (bulk (paritySlotPerm f x).2) := by
    rw [hf]
    rfl
  have hparity := (paritySlotPerm_preserves_parity e x).trans
    (paritySlotPerm_preserves_parity f x).symm
  obtain ⟨j, b, hj⟩ := scheduledMatchedGraph_changed_code role pivot n
    (selectedPairMatching role n m bulk hbulk e f) anchor ha hp
    (bulk (paritySlotPerm e x).2) (bulk (paritySlotPerm f x).2)
    (hbulk (paritySlotPerm e x).2) (hbulk (paritySlotPerm f x).2)
    (parityPathValue (paritySlotPerm e x).1) (parityPathValue (paritySlotPerm f x).1)
    h rfl hpath hparity hx
  refine ⟨h, j, b, (paritySlotPerm e x).2, ?_, hj⟩
  exact copyScheduleOrigin_path (n + 1) _ _

theorem selectedFinalPerm_inv {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) :
    selectedFinalPerm role n m bulk hbulk (e⁻¹) = (selectedFinalPerm role n m bulk hbulk e).symm := by
  unfold selectedFinalPerm
  rw [paritySlotPerm_inv]
  rfl

theorem selectedFinalRelativePerm_matching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e f : FinalParityReassignments n m) :
    selectedFinalRelativePerm role n m bulk hbulk e f =
      scheduledHMatching role (n + 1) (selectedPairMatching role n m bulk hbulk (e⁻¹) (f⁻¹)) := by
  change (scheduledHMatching role (n + 1) (selectedFinalPerm role n m bulk hbulk f)).trans
    (scheduledHMatching role (n + 1) (selectedFinalPerm role n m bulk hbulk e)).symm = _
  rw [scheduledHMatching_symm, scheduledHMatching_trans]
  unfold selectedPairMatching
  rw [selectedFinalPerm_inv, selectedFinalPerm_inv, Equiv.symm_symm]

/-- The long prime is certified to be a selected bulk prime, so no upper
prime-range hypothesis is imposed on the top slot. -/
theorem selected_final_relative_prime_ranges {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (Q : I → Finset ℕ) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (lower : ℝ) (Bq A E : ℕ)
    (hsquare : ∀ j q, q ∈ Q (anchor j) → χ (anchor j) q ^ 2 ≠ 1)
    (hanchor : ∀ j q, q ∈ Q (anchor j) → lower ≤ (q : ℝ) ∧ q ≤ Bq)
    (hword : ∀ i p, p ∈ Q (bulk i) → 2 * A ≤ p ∧ p ≤ E)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ a b : CopyScheduleAtoms role (n + 1), a ≠ b ∧
      (∀ q ∈ Q (copyScheduleOrigin (n + 1) a.val), lower ≤ (q : ℝ) ∧ q ≤ Bq) ∧
      (∀ p ∈ Q (copyScheduleOrigin (n + 1) b.val), 2 * A ≤ p ∧ p ≤ E) ∧
      (let G := graphDifference (scheduledSurvivorGraph role pivot (n + 1))
        (transportGraph (selectedFinalRelativePerm role n m bulk hbulk e f)
          (scheduledSurvivorGraph role pivot (n + 1)))
       (∀ q ∈ Q (copyScheduleOrigin (n + 1) a.val),
         χ (copyScheduleOrigin (n + 1) a.val) q ^ G a b ≠ 1) ∧ G b a = 0) := by
  have hinv : e⁻¹ ≠ f⁻¹ := fun h => hef (inv_injective h)
  obtain ⟨h, j, sign, i, horig, hfwd, hrev⟩ :=
    selected_final_pair_interaction role pivot n m bulk hbulk anchor ha hp (e⁻¹) (f⁻¹) hinv
  let a := scheduledRetainedEmbedding role (n + 1)
    (.inr (scheduledPastAnchor role n (anchor j) j (ha j) sign))
  let b := scheduledRetainedEmbedding role (n + 1) (.inl h)
  have haorig : copyScheduleOrigin (n + 1) a.val = anchor j :=
    copyScheduleOrigin_anchor (n + 1) j sign (anchor j)
  have hborig : copyScheduleOrigin (n + 1) b.val = bulk i := horig
  refine ⟨a, b, (scheduledRetainedEmbedding role (n + 1)).injective.ne (by simp), ?_, ?_, ?_, ?_⟩
  · rw [haorig]
    exact hanchor j
  · rw [hborig]
    exact hword i
  · intro q hq
    rw [selectedFinalRelativePerm_matching, scheduledHMatching_graph]
    apply signed_square_nonprincipal _ _ _ hfwd
    rw [haorig] at hq ⊢
    exact hsquare j q hq
  · rw [selectedFinalRelativePerm_matching, scheduledHMatching_graph]
    exact hrev

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedFinalPairReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative reindexing of actual selected-bulk final pairs -/
namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem selectedFinalRelativePerm_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) (e f : FinalParityReassignments n m)
    (i : CopyScheduleAtoms role (n + 1)) :
    copyScheduleOrigin (n + 1) (selectedFinalRelativePerm role n m bulk hbulk e f i).val =
      copyScheduleOrigin (n + 1) i.val := by
  have hi := selectedFullFinalPerm_origin role n m bulk hbulk e
    ((selectedFullFinalPerm role n m bulk hbulk e).symm (selectedFullFinalPerm role n m bulk hbulk f i))
  rw [Equiv.apply_symm_apply] at hi
  exact hi.symm.trans (selectedFullFinalPerm_origin role n m bulk hbulk f i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedFinalPairDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Final parity pairs: cancellation for the actual scheduled constituents -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

/-- All distinct final parity arrangements satisfy the original-prior pair estimate.
The one-sided character, word sizes, range counts and common modulus are derived
from the actual schedule; only the explicit physical prime and frequency ranges remain. -/
theorem eventual_selected_final_pair_decay {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Aw Kr : ℕ) (s C S H z α β γ c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα : 0 < α) (hαβ : α < β) (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (size : I → ℕ) (Smax : ℕ) (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M))
      (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (pivot : ℕ → (Σ i, Fin (size i)))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n + 1, ∀ r ∈ ranges j, r.atoms.length ≤ Aw)
      (_hcount : ∀ j ≤ n + 1, (ranges j).length ≤ Kr)
      (ψ : 𝓢(ℝ, ℂ)) (_hreal : ∀ y, conj (ψ y) = ψ y)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hX : 0 < X) (_hXlo : 1 < X * lo)
      (_hu : ∀ j < n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let FP := WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀ (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (hbulk : ∀ i, ρ (bulk i) = .word)
      (anchor : Fin (n + 1) → (Σ a, Fin (size a)))
      (_ha : ∀ j, ρ (anchor j) = .anchor j) (_hp : ∀ j < n + 1, ρ (pivot j) = .pivot j)
      (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
      (Q : (Σ i, Fin (size i)) → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
      (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
      (A E Bq : ℕ) (_hA : 0 < A) (lower V R : ℝ)
      (_hlower : 0 < lower) (_hV : 0 < V) (_hR : 3 ≤ R)
      (_hsquare : ∀ j q, q ∈ Q (anchor j) → χ (anchor j) q ^ 2 ≠ 1)
      (_hanchor : ∀ j q, q ∈ Q (anchor j) → lower ≤ (q : ℝ) ∧ q ≤ Bq)
      (_hword : ∀ i p, p ∈ Q (bulk i) → 2 * A ≤ p ∧ p ≤ E)
      (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
      (cutoff : ℕ → ℕ) (_hcutoff : Monotone cutoff)
      (_hVfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * (1 + M)))
      (_hs₀ : SchwartzMap.seminorm ℝ 0 0 FP.profile ≤ S)
      (_hs₁ : SchwartzMap.seminorm ℝ 0 1 FP.profile ≤ S)
      (_hwidth : ∀ i, FP.upper i - FP.lower i ≤ Real.exp (C * (1 + M)))
      (_hE : ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hQinv : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
      (_hshort : Real.exp (c * Real.exp (α * L)) ≤ lower)
      (_hlong : Real.exp (Real.exp (β * L)) ≤ (A : ℝ))
      (_hBqscale : (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)))
      (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α * L)) ≤ (p : ℝ))
      (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
      (e f : FinalParityReassignments n m) (_hef : e ≠ f)
      (d d' : ScheduledFrequencyIndex cutoff (n + 1))
      (_hroot : scheduledRootIndex cutoff (n + 1) d = scheduledRootIndex cutoff (n + 1) d')
      (_hlarge : ∀ p ∈ P, cutoff (n + 1) < p)
      (center : ∀ p : ℕ, ZMod p),
    ‖∑ q : SurvivingConstituent role size (n + 1) → P,
      ((∏ i, primeSubsetPrior P (Q (copyScheduleOrigin (n + 1) i.val)) (q i) : ℝ) : ℂ) *
      (constituentPrimeTerm role size χ κ pivot (n + 1) P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center (scheduledFrequencyHistory cutoff (n + 1) d) q *
      conj (constituentPrimeTerm role size χ κ pivot (n + 1) P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center (scheduledFrequencyHistory cutoff (n + 1) d')
          (fun i => q (selectedFinalRelativePerm ρ n m bulk hbulk e f i))))‖ ≤
        Real.exp (-(c / 32) * Real.exp (α * L)) := by
  let a₀ := constituentFinalCountRate (Fintype.card I) (n + 1) s
  let b₀ := (((2 * 3 ^ (n + 1) * Fintype.card I + Aw : ℕ) : ℝ) * s + 4)
  let d₀ : ℝ := (Kr * (2 ^ (n + 1 + 1) - 1) + 1 : ℕ)
  have ha₀ : 0 ≤ a₀ := constituentFinalCountRate_nonneg _ _ _ hs
  have hb₀ : 0 ≤ b₀ := by dsimp [b₀]; positivity
  have hd₀ : 0 ≤ d₀ := by dsimp [d₀]; positivity
  filter_upwards [eventual_constituent_final_pair_decay (n + 1) a₀ b₀ d₀ C S H z α β γ c
      ha₀ hb₀ hd₀ hC hS hH hz hα hαβ hγβ hc,
    eventual_final_pair_period_scale (n + 1) b₀ C z β hb₀ hC hz (hα.trans hαβ)]
    with L hdec hperiod
  intro size Smax hSmax hsize M hm hmL hSm χ κ hκ pivot childBound pivotBound ranges hrange
    hcount ψ hreal X lo hi hlo hhi hX hXlo hu ρ FP m bulk hbulk anchor ha hp P hP hprime Q hQP hQmass
    A E Bq hA lower V R hlower hV hR hsquare hanchor hword hlowerP hupperP cutoff hcutoff hVfreq
    hs₀ hs₁ hwidth hE hQinv hshort hlong hBqscale hmin hratio e f hef d d' hroot hlarge center
  let Vfreq := cutoff (n + 1)
  let t := scheduledFrequencyHistory cutoff (n + 1) d
  let t' := scheduledFrequencyHistory cutoff (n + 1) d'
  have hfv := scheduledFrequencyHistory_all_bound cutoff hcutoff (n + 1) d
  have hfv' := scheduledFrequencyHistory_all_bound cutoff hcutoff (n + 1) d'
  have hroot' := (scheduledRootIndex_eq_iff cutoff (n + 1) d d').mp hroot
  by_cases htzero : ∀ q : SurvivingConstituent role size (n + 1) → P,
      constituentPrimeTerm role size χ κ pivot (n + 1) P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t q = 0
  · dsimp only [t] at htzero
    simp only [htzero, zero_mul, mul_zero, Finset.sum_const_zero, norm_zero]
    exact Real.exp_nonneg _
  by_cases htzero' : ∀ q : SurvivingConstituent role size (n + 1) → P,
      constituentPrimeTerm role size χ κ pivot (n + 1) P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t' q = 0
  · dsimp only [t'] at htzero'
    simp only [htzero', map_zero, mul_zero, Finset.sum_const_zero, norm_zero]
    exact Real.exp_nonneg _
  push Not at htzero htzero'
  obtain ⟨q, hq⟩ := htzero
  obtain ⟨q', hq'⟩ := htzero'
  obtain ⟨ht, hn⟩ := constituentPrimeTerm_nonzero_frequencies role size χ κ pivot (n + 1)
    P hprime childBound pivotBound ranges ψ X lo hi hX hXlo center t q hq
  obtain ⟨ht', hn'⟩ := constituentPrimeTerm_nonzero_frequencies role size χ κ pivot (n + 1)
    P hprime childBound pivotBound ranges ψ X lo hi hX hXlo center t' q' hq'
  obtain ⟨hsmall, hfreq⟩ := finite_frequency_range_data P hP R Vfreq hlarge hupperP
    (n + 1) t hn hfv
  obtain ⟨hsmall', hfreq'⟩ := finite_frequency_range_data P hP R Vfreq hlarge hupperP
    (n + 1) t' hn' hfv'
  let perm := selectedFinalRelativePerm ρ n m bulk hbulk e f
  let W := primeWordEmbedding (scheduleConstituentWord role size (n + 1))
  let W' := primeWordEmbedding (fun v => List.map perm (scheduleConstituentWord role size (n + 1) v))
  let B := 2 * 3 ^ (n + 1) * Fintype.card I * Smax + Aw * Smax + 4
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBlinear : (B : ℝ) ≤ b₀ * (1 + M) :=
    constituent_word_budget_linear (n + 1) Aw Smax s M hSm hm
  obtain ⟨hw, hw', hD, hD', hU, hU'⟩ :=
    constituent_final_word_bounds role size (n + 1) perm childBound pivotBound ranges
      Smax Aw hSmax hsize hrange
  have hcounts := constituent_final_linear_counts role size (n + 1) perm Smax s M
    hSmax hsize hs hm hSm
  have hranges := expandedRootRanges_pair_linear_count role (n + 1) Kr W W' ranges hcount
    (originalProductRange ([] : List (Option (SurvivingConstituent role size (n + 1)))) (n + 1) 1 0) M hm
  obtain ⟨a, b, hab, haQ, hbQ, hnonprincipal, hreverse⟩ :=
    selected_final_relative_prime_ranges ρ pivot n m bulk hbulk anchor ha hp Q χ lower Bq A E
      hsquare hanchor hword e f hef
  have hχ : ∀ i, χ (copyScheduleOrigin (n + 1) (perm i).val) =
      χ (copyScheduleOrigin (n + 1) i.val) := by
    intro i
    rw [selectedFinalRelativePerm_origin]
  have hMA := hperiod M B Vfreq A t t' hm hmL hBlinear hVfreq hfv hfv' hlong
  exact hdec I role size χ κ pivot hκ perm hχ childBound pivotBound ranges ψ hreal X lo hi
    hlo hhi hu a b hab t t' ht ht' hroot' B hB hw hw' hD hD' hU hU' hreverse
    P hP hprime (fun i => Q (copyScheduleOrigin (n + 1) i.val))
    (fun i => hQP _) (fun i => hQmass _) hnonprincipal A E hA hMA hsmall hsmall'
    (fun p hp => (hbQ p hp).1) (fun p hp => (hbQ p hp).2) lower hlower
    (fun q hq => (haQ q hq).1) Bq (fun q => (haQ q.val q.property).2)
    V R hV hR hlowerP hupperP hfreq hfreq' M hm hmL Vfreq hBlinear
    hranges.1 hranges.2 hVfreq hfv hfv' hs₀ hs₁ hwidth hE (fun i => hQinv _)
    hshort hlong hBqscale hmin hratio hcounts.1 hcounts.2 center

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedNaturalFinalContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original final comparison from explicit prime-range data -/
namespace Ostmann
universe u
open Filter
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

/-- The final second-moment estimate has no assumed energy or pair bound.
The two thresholds are uniform over the growing word and constituent lists. -/
theorem selected_natural_final_contradiction {I : Type u} [Fintype I]
    (role : I → CopyScheduleRole) (n Aw Kr : ℕ) (s C S H z α β γ c : ℝ)
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hS : 1 ≤ S) (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hα : 0 < α) (hαβ : α < β) (hγβ : γ < β) (hc : 0 < c)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (C₀ K d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (B₁ Cfinal : ℝ) (hB₁ : 0 ≤ B₁)
    (hentropy : Cfinal + (d + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ (size : I → ℕ) (Smax : ℕ) (_hSmax : 1 ≤ Smax) (_hsize : ∀ i, size i ≤ Smax)
      (M : ℝ) (_hM₀ : M₀ ≤ M) (_hm : 0 ≤ M) (_hmL : M ≤ z * L) (_hSm : (Smax : ℝ) ≤ s * (1 + M)),
    let cutoff := naturalTransferCutoff (d * M) M
    ∀       (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
      (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (_hκ : ∀ i p, ‖κ i p‖ ≤ 1)
      (pivot : ℕ → (Σ i, Fin (size i)))
      (childBound pivotBound : ℕ → ℕ)
      (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
      (_hrange : ∀ j ≤ n + 1, ∀ r ∈ ranges j, r.atoms.length ≤ Aw)
      (_hcount : ∀ j ≤ n + 1, (ranges j).length ≤ Kr)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (_hX : 0 < X) (_hXlo : 1 < X * lo)
      (_hu : ∀ j < n + 1, ∀ a b, role a = .pivot j → role b = .pivot j → a = b),
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let FP := WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
    ∀ (m : ℕ) (bulk : Fin m ↪ (Σ a, Fin (size a))) (_hbulk : ∀ i, ρ (bulk i) = .word)
      (anchor : Fin (n + 1) → (Σ a, Fin (size a)))
      (_ha : ∀ j, ρ (anchor j) = .anchor j) (_hp : ∀ j < n + 1, ρ (pivot j) = .pivot j)
      (P : Finset ℕ) (_hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
      (Q : (Σ i, Fin (size i)) → Finset ℕ) (_hQP : ∀ i, Q i ⊆ P)
      (_hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
      (A E Bq : ℕ) (_hA : 0 < A) (lower V R : ℝ)
      (_hlower : 0 < lower) (_hV : 0 < V) (_hR : 3 ≤ R)
      (_hsquare : ∀ j q, q ∈ Q (anchor j) → χ (anchor j) q ^ 2 ≠ 1)
      (_hanchor : ∀ j q, q ∈ Q (anchor j) → lower ≤ (q : ℝ) ∧ q ≤ Bq)
      (_hword : ∀ i p, p ∈ Q (bulk i) → 2 * A ≤ p ∧ p ≤ E)
      (_hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (_hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
      (_hVfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * M))
      (_hs₀ : SchwartzMap.seminorm ℝ 0 0 FP.profile ≤ S)
      (_hs₁ : SchwartzMap.seminorm ℝ 0 1 FP.profile ≤ S)
      (_hwidth : ∀ i, FP.upper i - FP.lower i ≤ Real.exp (C * (1 + M)))
      (_hE : ((Nat.log 2 E + 1 : ℕ) : ℝ) ≤ Real.exp (H * (1 + M)))
      (_hQinv : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp (H * (1 + M)))
      (_hshort : Real.exp (c * Real.exp (α * L)) ≤ lower)
      (_hlong : Real.exp (Real.exp (β * L)) ≤ (A : ℝ))
      (_hBqscale : (Bq : ℝ) ≤ Real.exp (Real.exp (γ * L)))
      (_hmin : ∀ p ∈ P, Real.exp (c * Real.exp (α * L)) ≤ (p : ℝ))
      (_hratio : Real.log R / V ≤ Real.exp (H * (1 + M)))
      (_hlarge : ∀ p ∈ P, cutoff (n + 1) < p)
      (i : Σ a, Fin (size a)) (_hi : role i.1 = .word)
      (_hlo₀ : Real.exp (d * M - C₀) ≤ lo)
      (h J : ℕ)
      (_hmod : cutoff (n + 1) ^ ((2 ^ (n + 2) - 1) * (n + 3)) ≤ 2 ^ h)
      (_hcellrange : ∀ p ∈ Q i, 2 ^ h ≤ p ∧ p < 2 ^ (h + J))
      (a C₁ : ℝ) (_ha₀ : 0 < a) (_hL : 1 ≤ L)
      (_hcellmass : a ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹) (_hJ : (J : ℝ) ≤ Real.exp (C₁ * L))
      (center : ∀ p : ℕ, ZMod p),
    ∀ (_hMm : M = (m : ℝ)) (_hLm : L ≤ (m : ℝ)) (_hC₁ : 0 ≤ C₁)
    (_hcost : C₁ + max (Real.log (3 / a)) 0 + ε ≤ Cfinal)
    (_hlower : Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤ ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hprime Q
        childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
        (scheduledFrequencyHistory cutoff (n + 1)) center‖), False := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    (eventual_selected_final_natural_energy_comparison n ψ C₀ K d ε hd hε hψ)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (eventual_rounded_frequency_card (n + 1) d hd)
  refine ⟨max M₀ R₀, ?_⟩
  filter_upwards [eventual_selected_final_pair_decay role n Aw Kr s C S H z α β γ c
    hs hC hS hH hz hα hαβ hγβ hc,
    eventual_scheduled_final_contradiction n B₁ (d + 1) Cfinal 1 z α (c / 32)
      hB₁ (by linarith) (by norm_num) hz hα (by positivity) hentropy] with L hdec hcontra
  intro size Smax hSmax hsize M hMlarge hm hmL hSm cutoff χ κ hκ pivot childBound pivotBound ranges
    hrange hcount X lo hi hlo hhi hX hXlo hu ρ FP m bulk hbulk anchor ha hp P hP hprime
    Q hQP hQmass A E Bq hA lower V R hlower hV hR hsquare hanchor hword hlowerP hupperP
    hVfreq hs₀ hs₁ hwidth hE hQinv hshort hlong hBqscale hmin hratio
    hlarge i hiword hlo₀ h J hmod hcellrange a C₁ ha₀ hL hcellmass hJ center hMm hLm hC₁ hcost hamp
  have hcutoff : Monotone cutoff := naturalTransferCutoff_monotone _ _ (mul_nonneg hd hm)
  have hfreq : (cutoff (n + 1) : ℝ) ≤ Real.exp (C * (1 + M)) := by
    apply hVfreq.trans
    apply Real.exp_le_exp.mpr
    nlinarith only [hC]
  have hpairs := hdec size Smax hSmax hsize M hm hmL hSm χ κ hκ pivot childBound pivotBound
    ranges hrange hcount ψ hreal X lo hi hlo hhi hX hXlo hu m bulk hbulk anchor ha hp P hP hprime
    Q hQP hQmass A E Bq hA lower V R hlower hV hR hsquare hanchor hword hlowerP hupperP
    cutoff hcutoff hfreq hs₀ hs₁ hwidth hE hQinv hshort hlong hBqscale hmin hratio
  have hupper := hM₀ M ((le_max_left _ _).trans hMlarge) role size χ κ hκ pivot childBound pivotBound ranges i hiword hu m bulk hbulk
    X lo hi P (fun p hp => ⟨hprime p hp, hlarge p hp⟩) Q
    hX hXlo hlo₀ hQP (fun i => ne_of_gt (hQmass i)) h J hmod hcellrange a C₁ L ha₀ hL
    hcellmass hJ center _ (Real.exp_nonneg _)
    (fun e f hef d d' hd => hpairs e f hef d d' hd hlarge center)

  have hcard₀ := hR₀ M ((le_max_right _ _).trans hMlarge) (n + 1) le_rfl
  have hcard : ((transferFrequencyRange (cutoff (n + 1))).card : ℝ) ≤
      Real.exp ((d + 1) * (2 ^ (n + 1) : ℝ) * m) := by
    apply hcard₀.trans
    apply Real.exp_le_exp.mpr
    have hp : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
    rw [hMm]
    have hmul := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [hmul]
  have he : (C₁ + max (Real.log (3 / a)) 0) * (2 ^ (n + 1) : ℕ) * L + ε * M ≤
      Cfinal * (2 ^ (n + 1) : ℝ) * m := by
    rw [hMm]
    have hh := selected_prime_energy_exponent_le n m L
      (C₁ + max (Real.log (3 / a)) 0) ε
      (add_nonneg hC₁ (le_max_right _ _)) hε.le hLm
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcost (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1)))
      (Nat.cast_nonneg m))
  have hcompare := hupper.trans (mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he)
      (Nat.cast_nonneg _)) le_rfl) (Nat.cast_nonneg _))
  have hlog : Real.log 2 < (1 : ℝ) := by
    exact (Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)).trans_le (by norm_num)
  have hmone : 1 ≤ (m : ℝ) := (le_trans (show (1 : ℝ) ≤ L from hL) hLm)
  have hmargin : Real.log 2 < 1 * (2 ^ (n + 1) : ℝ) * m := by
    have hp : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [hlog, hmone, hmul]
  apply hcontra m cutoff _ hcutoff ?_ hcard hmargin hamp hcompare
  simpa only [hMm] using hmL

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFinalContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The final comparison at the literal signed character prior -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_character_final_contradiction_oai (n N : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x)
    (K B B₁ z c Cmass α βg βw γs νw ε : ℝ)
    (hB : 1 ≤ B) (hB₁ : 0 ≤ B₁) (hz : 1 ≤ z) (hc : 1 ≤ c)
    (hCmass : 0 < Cmass) (hα : 0 < α) (hβg : 0 < βg)
    (hαw : α < βw) (hsw : γs < βw) (hβw : βw < νw) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1) :
    ∃ M₀ : ℝ, ∀ᶠ L : ℝ in atTop, ∀ m : ℕ, M₀ ≤ (m : ℝ) →
      L ≤ m → (m : ℝ) ≤ z * L →
      ∀ (r : Fin (n + 1) → ℕ) (f : ℕ) (hr : ∀ j, 0 < r j),
      (∀ j, r j ≤ N) → f ≤ N →
      ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
        (Q : (Σ v, Fin (characterSize m r f v)) → Finset ℕ),
      (∀ i, Q i ⊆ P) →
      (∀ i, Real.exp (-Cmass * L) ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹) →
      (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
      (∀ j p, p ∈ Q (characterAnchor m r f j false) →
        (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) →
      (∀ i p, p ∈ Q (characterBulk m r f i) → Real.exp (Real.exp (νw * L)) ≤ p) →
      (∀ i : Fin m, 1 ≤ ∑ p ∈ Q (characterBulk m r f i), (p : ℝ)⁻¹) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (J : ℕ) (lower upper : CharacterCell (n + 1) → ℕ) (logX : ℝ), 0 < logX →
      let Δ := characterBaseGap B z m
      let lo := initialWordAtomLower J lower
      let hi := initialWordAtomUpper J upper
      let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
      let V := naturalTransferCutoff Δ m
      ∀ (cap : ℕ → ℕ) (center : ∀ p : ℕ, ZMod p),
      Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤
        ‖scheduledConstituentAmplitude (characterRole (n + 1)) (characterSize m r f) χ₀
          (fun i => primeGaussMultiplier (χ₀ i)) (characterPivot m r f hr) P hP Q lo hi V cap
          (scheduleFourierLeaf (characterRole (n + 1)) ψ (Real.exp logX)
            (Real.exp (Δ - (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))
            (Real.exp (Δ + (Fintype.card (CharacterRole (n + 1)) : ℝ) * c))) center (n + 1)‖ →
      False := by
  let d := B + 20 * Real.log z
  let C₀ := (Fintype.card (CharacterRole (n + 1)) : ℝ) * c
  let D := (2 : ℝ) ^ (n + 1) * d + 2 * (4 : ℝ) ^ (n + 1)
  let C := max D (d + 1)
  let C₁ := βg + Real.log ((Real.log 2)⁻¹ + 1)
  let H := Cmass + βg + α + Real.log ((Real.log 2)⁻¹ + 1) + 2
  let S := max 1 (max (SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)))
    (SchwartzMap.seminorm ℝ 0 1 (𝓕 ψ : 𝓢(ℝ, ℂ))))
  have hz0 : 0 < z := by linarith
  have hd1 : 1 ≤ d := by dsimp [d]; linarith [Real.log_nonneg hz]
  have hd : 0 ≤ d := by linarith
  have hC : 0 ≤ C := (by dsimp [D]; positivity : (0 : ℝ) ≤ D).trans (le_max_left _ _)
  have hlc : 0 ≤ Real.log ((Real.log 2)⁻¹ + 1) := by
    have hh : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_pos (by norm_num)).le
    exact Real.log_nonneg (by linarith)
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; linarith
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hHm : Cmass ≤ H := by dsimp [H]; linarith
  have hHdy : βg + Real.log ((Real.log 2)⁻¹ + 1) ≤ H := by dsimp [H]; linarith
  have hHratio : βg - α ≤ H := by dsimp [H]; linarith
  obtain ⟨M₁, hcontra⟩ := selected_natural_final_contradiction (characterRole (n + 1)) n 1
    (3 ^ (n + 1) * Fintype.card (CharacterRole (n + 1))) ((N : ℝ) + 2) C S H z
    α βw γs 1 (by positivity) hC (le_max_left _ _) hH hz0.le hα hαw hsw (by norm_num)
    ψ hreal C₀ K d ε hd hε B₁ (C₁ + max (Real.log 3) 0 + ε) hB₁
    (by exact hentropy) hψ
  refine ⟨max M₁ (max 1 C₀), ?_⟩
  filter_upwards [hcontra,
    eventual_character_band_lower βw νw (hα.trans (hαw.trans hβw)) hβw,
    eventual_natural_cutoff_below_primes (n + 1) d z α 1 hd hz0.le hα (by norm_num),
    eventual_character_energy_prime_range (n + 1) ((2 ^ (n + 2) - 1) * (n + 3))
      d z α βg hd hz0.le hα hβg.le,
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hβg)).eventually
      (eventually_ge_atTop (2 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with L hcontra hAw hlarge hdyadic hRthree hL
  intro m hM hLM hmL r f hr hrN hf P hP Q hQP hmass hPrange hsmall hword hbulk
    χ hχ J lower upper logX hlogX Δ lo hi χ₀ V cap center hamp
  have hm : (1 : ℝ) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hM₁ : M₁ ≤ (m : ℝ) := (le_max_left _ _).trans hM
  have hCm : C₀ ≤ (m : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hms : 0 < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  let i : Fin m := ⟨0, hms⟩
  have hpos (i) : 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹ := (Real.exp_pos _).trans_le (hmass i)
  have hPne : P.Nonempty := by
    have hne : Q (characterTop m r f) ≠ ∅ := by
      intro he
      have hh := hpos (characterTop m r f)
      simp only [he, Finset.sum_empty, lt_self_iff_false] at hh
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact ⟨q, hQP _ hq⟩
  let A := ⌈Real.exp (Real.exp (βw * L))⌉₊
  let E := ⌊Real.exp (Real.exp (βg * L))⌋₊
  let Bq := ⌊Real.exp (Real.exp (γs * L))⌋₊
  let ℓ := Real.exp (Real.exp (α * L))
  let Rmax := Real.exp (Real.exp (βg * L))
  have hE : (E : ℝ) ≤ Rmax := Nat.floor_le (Real.exp_nonneg _)
  have hWB := character_initial_window_bounds d C₀ m hd1 hm (by dsimp [C₀]; positivity) hCm
  change 1 ≤ Real.exp (Δ - C₀) ∧ Real.exp (Δ - C₀) ≤ Real.exp (Δ + C₀) ∧
    Real.exp (Δ + C₀) - Real.exp (Δ - C₀) ≤ Real.exp ((d + 1) * m) at hWB
  have hXlo : 1 < Real.exp logX * Real.exp (Δ - C₀) := by
    have he := Real.one_lt_exp_iff.mpr hlogX
    have hlo := hWB.1
    nlinarith only [he, hlo]
  have huniq : ∀ j < n + 1, ∀ u v, characterRole (n + 1) u = .pivot j →
      characterRole (n + 1) v = .pivot j → u = v := by
    intro j hj u v hu hv
    exact (characterPivotAtom_unique ⟨j, hj⟩ u hu).trans (characterPivotAtom_unique ⟨j, hj⟩ v hv).symm
  have hcounts := character_interval_complexity (n + 1) (n + 1) le_rfl lo hi
  have hfreq : (V (n + 1) : ℝ) ≤ Real.exp (C * (m : ℝ)) := by
    apply (naturalTransferCutoff_linear_bound (n + 1) (n + 1) d m le_rfl hd hm).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hwidth : ∀ j, (WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ))
      (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1).upper j -
      (WordFourierParameters.uniform (n + 1) (𝓕 ψ : 𝓢(ℝ, ℂ))
      (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1).lower j ≤
        Real.exp (C * (1 + (m : ℝ))) := by
    intro j
    apply hWB.2.2.trans
    apply Real.exp_le_exp.mpr
    have hdC := le_max_right D (d + 1)
    nlinarith only [hdC, hC, Nat.cast_nonneg (α := ℝ) m]
  obtain ⟨h, JJ, hmod, hrange, hJJ⟩ := hdyadic (m : ℝ) hm hmL (Q (characterBulk m r f i))
    (fun q hq => hPrange q (hQP _ hq))
  exact hcontra (characterSize m r f) (m + N + 1) (by omega)
    (characterSize_le (n + 1) m N r f hrN hf) m hM₁ (Nat.cast_nonneg _) hmL
    (characterSize_linear_bound m N) χ₀ (fun i => primeGaussMultiplier (χ₀ i))
    (fun i p => (primeGaussMultiplier_norm _ _).le) (characterPivot m r f hr) V cap
    (atomIntervalRanges (characterRole (n + 1)) lo hi) hcounts.1 hcounts.2
    (Real.exp logX) (Real.exp (Δ - C₀)) (Real.exp (Δ + C₀)) hWB.1 hWB.2.1
    (Real.exp_pos _) hXlo huniq m (characterBulk m r f) (characterBulk_role m r f)
    (fun j => characterAnchor m r f j false) (fun j => rfl)
    (fun j hj => characterPivot_role m r f hr j hj) P hPne hP Q hQP hpos
    A E Bq hAw.1 ℓ (Real.exp (α * L)) Rmax (Real.exp_pos _) (Real.exp_pos _)
    (by
      have hh : 2 ≤ Real.exp (βg * L) := by simpa only [Function.comp_apply, id_eq] using hRthree
      have he := Real.add_one_le_exp (Real.exp (βg * L))
      linarith)
    (fun j q hq => hχ q (hQP _ hq))
    (fun j q hq => ⟨(hPrange q (hQP _ hq)).1, Nat.le_floor (hsmall j q hq)⟩)
    (fun j q hq => ⟨hAw.2.2 q (hword j q hq), Nat.le_floor (hPrange q (hQP _ hq)).2⟩)
    (fun q hq => (Real.le_log_iff_exp_le (by exact_mod_cast (hP q hq).pos)).mpr (hPrange q hq).1)
    (fun q hq => (hPrange q hq).2) hfreq
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _)) hwidth
    (character_prime_band_dyadic_budget E βg L m H hβg.le hL hLM hHdy hH hE)
    (fun i => (harmonic_mass_inv_energy_budget (Q i) Cmass L m hCmass.le hLM (hmass i)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hHm (by linarith))))
    (by simp only [one_mul]; exact le_rfl) hAw.2.1 (Nat.floor_le (Real.exp_nonneg _))
    (fun q hq => by simpa only [one_mul] using (hPrange q hq).1)
    (character_prime_band_log_ratio α βg L m H (by linarith) hLM hβg.le hHratio hH)
    (fun q hq => hlarge _ hm hmL q (by simpa only [one_mul] using (hPrange q hq).1) _ le_rfl)
    (characterBulk m r f i) rfl le_rfl h JJ (hmod (n + 1) le_rfl) hrange
    1 C₁ (by norm_num) hL (hbulk i) hJJ center rfl hLM hC₁
    (by simp only [div_one]; exact le_rfl) hamp

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.eventual_character_final_contradiction_oai := @OAI.Ostmann.eventual_character_final_contradiction_oai
