-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.moving_pattern_diagonal_haar_rate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:28:40.679819+00:00
-- url     : https://prove2.me/submissions/79dab070-880a-4f63-b9ee-cf691414661d

import Mathlib
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_moving_outer_coprime_mixed_haar_rate

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CRTResidueAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact independent residue averages from the Chinese remainder theorem -/

namespace Ostmann

open scoped BigOperators

theorem crtUnitEquiv_apply {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (u : (ZMod (∏ i, a i))ˣ) (i : I) :
    crtUnitEquiv a hc u i = Units.map
      ((ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i))).toMonoidHom) u := by
  apply Units.ext
  change ZMod.prodEquivPi a hc (u : ZMod (∏ i, a i)) i = _
  exact ZMod.prodEquivPi_apply a hc u i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CRTLineAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint CRT factorization in the two giant environments -/

namespace Ostmann

open scoped BigOperators

theorem uniform_equiv_pi_average {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] {X : I → Type*} [∀ i, Fintype (X i)]
    (e : A ≃ ∀ i, X i) (f : ∀ i, X i → ℝ) :
    (Fintype.card A : ℝ)⁻¹ * (∑ a, ∏ i, f i (e a i)) =
      ∏ i, (Fintype.card (X i) : ℝ)⁻¹ * ∑ x, f i x := by
  classical
  rw [e.sum_comp (fun x => ∏ i, f i (x i)), Fintype.card_congr e, Fintype.card_pi]
  rw [← Fintype.prod_sum]
  simp only [Nat.cast_prod, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem crtExternalPairEquiv_apply {I : Type*} [Fintype I] (a : I → ℕ)
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (u : ZMod (∏ i, a i)) (v : (ZMod (∏ i, a i))ˣ) (i : I) :
    crtExternalPairEquiv a hc (u, v) i = (ZMod.prodEquivPi a hc u i, crtUnitEquiv a hc v i) := rfl

/-- The same exact factorization with the first giant an external integer. -/
theorem crt_external_pair_average {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℕ) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (f : ∀ i, ZMod (a i) × (ZMod (a i))ˣ → ℝ) :
    (Fintype.card (ZMod (∏ i, a i) × (ZMod (∏ i, a i))ˣ) : ℝ)⁻¹ *
      (∑ z, ∏ i, f i (crtExternalPairEquiv a hc z i)) =
    ∏ i, (Fintype.card (ZMod (a i) × (ZMod (a i))ˣ) : ℝ)⁻¹ * ∑ z, f i z :=
  uniform_equiv_pi_average (crtExternalPairEquiv a hc) f

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the Fourier matrix of the affine action

The finite matrix from `AffineFourier` is the action of
`F(t) ↦ ∑ c(a,b) F(at+b)` on nonzero additive frequencies.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_units_eq_sum_of_zero {p : ℕ} [Fact p.Prime]
    {R : Type*} [AddCommMonoid R] (F : ZMod p → R) (hF : F 0 = 0) :
    (∑ u : (ZMod p)ˣ, F u) = ∑ x : ZMod p, F x := by
  classical
  calc
    _ = ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, F x := by
      apply Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p))
      · intro u _
        exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
      · intro u _ v _ huv
        exact Units.val_injective huv
      · intro x hx
        refine ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
      · intro _ _
        rfl
    _ = ∑ x : ZMod p, F x := by
      simpa only [hF, add_zero] using
        Finset.sum_erase_add (Finset.univ : Finset (ZMod p)) F (Finset.mem_univ 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping the exceptional-character density in the arithmetic measures

The correction is retained, including when it correlates with the amplitude.
Once its conductor is supported on the frequency modulus, CRT places it in
that coordinate and the other residue averages factor exactly.
-/

namespace Ostmann

open scoped BigOperators

/-- Exact separation of a retained density and all remaining coordinates.
This also applies to signed and complex amplitudes. -/
theorem uniform_equiv_product_average {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B × C) (f : B → ℂ) (g : C → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * (∑ a, f (e a).1 * g (e a).2) =
      ((Fintype.card B : ℂ)⁻¹ * ∑ b, f b) *
        ((Fintype.card C : ℂ)⁻¹ * ∑ c, g c) := by
  rw [e.sum_comp (fun z => f z.1 * g z.2), Fintype.card_congr e,
    Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RegularResidueNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaged regular-transform norm on the actual CRT residue classes

The sum of the nonnegative residue test is the squarefree modulus itself.
Consequently the progression errors are summed against its exact mass, with
no pointwise estimate on the small-prime transforms.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_regular_local_norm {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (g : ZMod p → ℂ) (hg : g 0 = 0) :
    (∑ u : (ZMod p)ˣ, ‖g ((a * u⁻¹ : (ZMod p)ˣ) : ZMod p)‖ ^ 2) =
      ∑ x : ZMod p, ‖g x‖ ^ 2 := by
  have h := ((Equiv.inv (ZMod p)ˣ).trans (Equiv.mulLeft a)).sum_comp
    (fun u : (ZMod p)ˣ => ‖g (u : ZMod p)‖ ^ 2)
  change (∑ u : (ZMod p)ˣ, ‖g ((a * u⁻¹ : (ZMod p)ˣ) : ZMod p)‖ ^ 2) = _ at h
  rw [h, sum_units_eq_sum_of_zero (fun x : ZMod p => ‖g x‖ ^ 2) (by simp [hg])]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RegularDiagonalCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cancellation of the diagonal regular-prime unit loss

The external integer giant is restricted to units. At a regular prime
carrying a squared transform, its energy cancels that restriction exactly.
At an outer compensation prime the factor left over is `1 - 1/p`.
-/

namespace Ostmann

open scoped BigOperators

theorem externalRegularLocal_sum_first {p : ℕ} [Fact p.Prime]
    (active : Bool) (a : (ZMod p)ˣ) (g : ZMod p → ℂ)
    (hg : g 0 = 0) (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) = p)
    (v : (ZMod p)ˣ) :
    (∑ x : ZMod p, externalRegularLocal active a g (x, v)) =
      if active then (p : ℝ) else Fintype.card (ZMod p)ˣ := by
  rw [← sum_units_eq_sum_of_zero
    (fun x => externalRegularLocal active a g (x, v)) (by simp [externalRegularLocal])]
  cases active
  · simp [externalRegularLocal, Units.ne_zero]
  · have hs := sum_regular_local_norm (a * v⁻¹) g hg
    rw [henergy] at hs
    simp only [↓reduceIte]
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro u _
    simp only [externalRegularLocal, Units.ne_zero, ↓reduceIte]
    simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]

theorem externalRegularLocal_average {p : ℕ} [Fact p.Prime]
    (active : Bool) (a : (ZMod p)ˣ) (g : ZMod p → ℂ)
    (hg : g 0 = 0) (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) = p) :
    (Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ)⁻¹ *
      (∑ z, externalRegularLocal active a g z) =
        if active then 1 else 1 - (p : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hu : (0 : ℝ) < Fintype.card (ZMod p)ˣ := by exact_mod_cast Fintype.card_pos
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [externalRegularLocal_sum_first active a g hg henergy]
  rw [Fintype.card_prod, ZMod.card, Nat.cast_mul]
  cases active
  · simp only [Bool.false_eq_true, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one] at *
    field_simp
  · simp only [↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- This is the exact regular-prime integral in the diagonal environment,
including the outer compensation slots which carry no transform. -/
theorem crt_external_regular_cancellation {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (active : I → Bool) (a : ∀ i, (ZMod (p i))ˣ) (g : ∀ i, ZMod (p i) → ℂ)
    (hg : ∀ i, g i 0 = 0) (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i) :
    (Fintype.card (ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) : ℝ)⁻¹ *
      (∑ z, ∏ i, externalRegularLocal (active i) (a i) (g i) (crtExternalPairEquiv p hc z i)) =
    ∏ i, if active i then 1 else 1 - (p i : ℝ)⁻¹ := by
  rw [crt_external_pair_average p hc (fun i => externalRegularLocal (active i) (a i) (g i))]
  apply Finset.prod_congr rfl
  intro i _
  exact externalRegularLocal_average (active i) (a i) (g i) (hg i) (henergy i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticCRTSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the regular-prime block from the signed arithmetic average -/

namespace Ostmann

open scoped BigOperators

/-- The signed remainder includes spectator, internal-prime and frequency
tests, including the retained Page correction. No absolute value is taken. -/
theorem crt_external_regular_with_remainder {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)]
    (hcop : (∏ i, p i).Coprime r)
    (active : I → Bool) (a : ∀ i, (ZMod (p i))ˣ) (g : ∀ i, ZMod (p i) → ℂ)
    (hg : ∀ i, g i 0 = 0) (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (F : ZMod r × (ZMod r)ˣ → ℂ) :
    (Fintype.card (ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ) : ℂ)⁻¹ *
      (∑ z,
        ((∏ i, externalRegularLocal (active i) (a i) (g i)
          (crtExternalPairEquiv p hc (crtSplitExternalEquiv (∏ i, p i) r hcop z).1 i) : ℝ) : ℂ) *
        F (crtSplitExternalEquiv (∏ i, p i) r hcop z).2) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ∑ z, F z) := by
  have hreg := crt_external_regular_cancellation p hc active a g hg henergy
  have hregC : (Fintype.card (ZMod (∏ i, p i) × (ZMod (∏ i, p i))ˣ) : ℂ)⁻¹ *
      (∑ z, ((∏ i, externalRegularLocal (active i) (a i) (g i)
        (crtExternalPairEquiv p hc z i) : ℝ) : ℂ)) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_sum] using congrArg (fun t : ℝ => (t : ℂ)) hreg
  rw [uniform_equiv_product_average (crtSplitExternalEquiv (∏ i, p i) r hcop)
    (fun z => ((∏ i, externalRegularLocal (active i) (a i) (g i)
      (crtExternalPairEquiv p hc z i) : ℝ) : ℂ)) F, hregC]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Arithmetic support at a reversing node

These are the elementary support facts preceding the progression estimate
in Section 8. The numerator is automatically coprime to inherited slots;
the remaining condition at a new prime is exactly nondivisibility by its square.
-/

namespace Ostmann

theorem reversal_numerator_coprime (v w HL HR : ℤ)
    (hLR : IsCoprime HL HR) (hv : IsCoprime v HL) (hw : IsCoprime w HR) :
    IsCoprime (v * HR - w * HL) HL ∧ IsCoprime (v * HR - w * HL) HR := by
  constructor
  · exact IsCoprime.sub_mul_right_left_iff.mpr (hv.mul_left hLR.symm)
  · exact IsCoprime.mul_sub_right_left_iff.mpr (hw.mul_left hLR)

/-- Both the inserted integer and its compensation product inherit all required coprimalities. -/
theorem reversal_inherited_coprime (v w HL HR s u p : ℤ)
    (hLR : IsCoprime HL HR) (hv : IsCoprime v HL) (hw : IsCoprime w HR)
    (hrel : v * HR - w * HL = s * u * p) :
    IsCoprime p (HL * HR) ∧ IsCoprime u (HL * HR) := by
  obtain ⟨hL, hR⟩ := reversal_numerator_coprime v w HL HR hLR hv hw
  have hboth := hL.mul_right hR
  rw [hrel] at hboth
  exact ⟨hboth.of_mul_left_right, hboth.of_mul_left_left.of_mul_left_right⟩

/-- A prime occurring once in `u` occurs once in the numerator exactly when it misses `p`. -/
theorem reversal_square_test (b s u p : ℕ) (hb : b.Prime)
    (hbs : ¬ b ∣ s) (hbu : b ∣ u) (hbu2 : ¬ b ^ 2 ∣ u) :
    (¬ b ^ 2 ∣ s * u * p) ↔ ¬ b ∣ p := by
  obtain ⟨v, rfl⟩ := hbu
  have hbv : ¬ b ∣ v := by
    intro hv
    apply hbu2
    simpa only [pow_two] using mul_dvd_mul_left b hv
  have heq : s * (b * v) * p = b * (s * v * p) := by ring
  rw [heq, pow_two, mul_dvd_mul_iff_left hb.ne_zero]
  simp only [hb.dvd_mul, hbs, hbv, or_self, false_or]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryResidueGate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the residue gate for cleared integer history tests -/

namespace Ostmann

open scoped Classical

theorem smallDivisionTest_modEq (N N' d : ℤ) (s : ℕ) (hd : d ≠ 0)
    (h : N ≡ N' [ZMOD d * s]) : smallDivisionTest N d s ↔ smallDivisionTest N' d s := by
  have hint : d ∣ N ↔ d ∣ N' := (h.of_dvd (dvd_mul_right d (s : ℤ))).dvd_iff
  have hquot (hN : d ∣ N) (hN' : d ∣ N') :
      (N / d : ℤ) ≡ N' / d [ZMOD s] := by
    apply Int.modEq_iff_dvd.mpr
    apply Int.dvd_of_mul_dvd_mul_left hd
    have he : d * (N' / d - N / d) = N' - N := by
      nlinarith only [Int.ediv_mul_cancel hN, Int.ediv_mul_cancel hN']
    rw [he]
    exact h.dvd
  constructor
  · rintro ⟨hN, hu⟩
    refine ⟨hint.mp hN, ?_⟩
    rwa [← (ZMod.intCast_eq_intCast_iff _ _ s).mpr (hquot hN (hint.mp hN))]
  · rintro ⟨hN', hu⟩
    refine ⟨hint.mpr hN', ?_⟩
    rwa [(ZMod.intCast_eq_intCast_iff _ _ s).mpr (hquot (hint.mpr hN') hN')]

theorem integerPolynomial_eval_modEq {σ : Type*} (P : MvPolynomial σ ℤ)
    (a b : σ → ℤ) (M : ℤ) (h : ∀ i, a i ≡ b i [ZMOD M]) :
    MvPolynomial.eval₂ (RingHom.id ℤ) a P ≡ MvPolynomial.eval₂ (RingHom.id ℤ) b P [ZMOD M] := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval₂_C, RingHom.id_apply]; exact .refl _
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp => simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul (h i)

theorem cleared_history_test_residue_invariant {σ : Type*} (P : MvPolynomial σ ℤ)
    (a b : σ → ℤ) (M : ℕ) (d : ℤ) (s : ℕ) (hd : d ≠ 0)
    (hdiv : d * s ∣ (M : ℤ)) (h : ∀ i, a i ≡ b i [ZMOD M]) :
    smallDivisionTest (MvPolynomial.eval₂ (RingHom.id ℤ) a P) d s ↔
      smallDivisionTest (MvPolynomial.eval₂ (RingHom.id ℤ) b P) d s :=
  smallDivisionTest_modEq _ _ d s hd ((integerPolynomial_eval_modEq P a b M h).of_dvd hdiv)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ClearedHistoryPivot
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed integer numerators for the recursive pivot substitutions -/

namespace Ostmann

open scoped BigOperators Classical

namespace ClearedHistoryValue

variable {σ : Type*}

theorem eval_variable (i : σ) (x : σ → ℚ) : (ofVariable i).eval x = x i := by
  simp only [eval, ofVariable, MvPolynomial.eval₂_X, Int.cast_one, div_one]

theorem eval_constant (a : ℤ) (x : σ → ℚ) : (constant a).eval x = a := by
  simp only [eval, constant, MvPolynomial.eval₂_C, Int.cast_one, div_one]
  rfl

theorem eval_prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ) (x : σ → ℚ) :
    (prod S f).eval x = ∏ i ∈ S, (f i).eval x := by
  simp only [eval, prod, MvPolynomial.eval₂_eq_eval_map, map_prod, Finset.prod_div_distrib]
  push_cast
  rfl

theorem eval_pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0)
    (x : σ → ℚ) :
    (pivot left right v w s hs).eval x = (v * right.eval x - w * left.eval x) / s := by
  have hL : (left.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr left.denominator_ne_zero
  have hR : (right.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr right.denominator_ne_zero
  have hS : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs
  simp only [eval, pivot, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, Int.coe_castRingHom, Int.cast_mul]
  field_simp

/-- Polynomial evaluation at an integer assignment is the numerator of the
actual rational value. The equality is useful on the integrality support. -/
theorem integer_value_cleared (F : ClearedHistoryValue σ) (x : σ → ℤ) (y : ℤ)
    (hy : F.eval (fun i => (x i : ℚ)) = y) :
    MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator = F.denominator * y := by
  have hden : (F.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr F.denominator_ne_zero
  have he : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator : ℚ) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.numerator := by
    simpa [Int.castRingHom] using
      (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.numerator)
  apply Int.cast_injective (α := ℚ)
  rw [he, Int.cast_mul]
  have hh := (div_eq_iff hden).mp hy
  simpa only [mul_comm] using hh

end ClearedHistoryValue

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistorySubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Substitution constructs the actual rational expressions of a reversed history -/

namespace Ostmann.HistoryFormula

variable {σ τ : Type*}

@[simp] theorem value_prime (i : σ) (x : σ → ℚ) : (prime i).value x = x i :=
  ClearedHistoryValue.eval_variable i x

@[simp] theorem value_external (z : ℤ) (x : σ → ℚ) : (external z).value x = z :=
  ClearedHistoryValue.eval_constant z x

@[simp] theorem value_product (l r : HistoryFormula σ) (x : σ → ℚ) :
    (product l r).value x = l.value x * r.value x := by
  simp only [value, cleared, ClearedHistoryValue.eval_prod, Fintype.prod_bool,
    Bool.false_eq_true, ite_false, if_false, ite_true, if_true]

@[simp] theorem value_solve (l r : HistoryFormula σ) (v w s : ℤ) (hs : s ≠ 0) (x : σ → ℚ) :
    (solve l r v w s hs).value x = (v * r.value x - w * l.value x) / s :=
  ClearedHistoryValue.eval_pivot l.cleared r.cleared v w s hs x

theorem value_bind (F : HistoryFormula σ) (f : σ → HistoryFormula τ) (x : τ → ℚ) :
    (F.bind f).value x = F.value (fun i => (f i).value x) := by
  induction F with
  | prime i => simp only [bind, value_prime]
  | external z => simp only [bind, value_external]
  | product l r hl hr => simp only [bind, value_product, hl, hr]
  | solve l r v w s hs hl hr => simp only [bind, value_solve, hl, hr]

theorem value_listProduct (fs : List (HistoryFormula σ)) (x : σ → ℚ) :
    (listProduct fs).value x = (fs.map (fun F => F.value x)).prod := by
  induction fs with
  | nil => simp [listProduct]
  | cons f fs ih => simp only [listProduct, value_product, List.map_cons, List.prod_cons, ih]

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerHistoryReconstruction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cleared formulas evaluate to the actual integer pivot reconstructions -/

namespace Ostmann

open scoped Classical

namespace HistoryPivotStep

variable {σ : Type*}

theorem formula_value (step : HistoryPivotStep σ) (x : σ → ℤ) :
    step.formula.value (fun i => (x i : ℚ)) = (step.numerator x : ℚ) / step.s := by
  have hp (l : List σ) : (l.map (fun i => (x i : ℚ))).prod = ((l.map x).prod : ℚ) := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  simp only [formula, HistoryFormula.value_solve, HistoryFormula.value_listProduct,
    List.map_map, Function.comp_def, HistoryFormula.value_prime, hp, numerator,
    Int.cast_sub, Int.cast_mul]

end HistoryPivotStep

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReconstructionIntegrality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every original integer-divisibility gate is a cleared polynomial test -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.integralAt_iff {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) :
    F.IntegralAt x ↔ F.cleared.denominator ∣
      MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, F.cleared.integer_value_cleared x y hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (div_eq_iff (Int.cast_ne_zero.mpr F.cleared.denominator_ne_zero)).mpr
    have he : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℚ) =
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.cleared.numerator := by
      simpa [Int.castRingHom] using
        (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.cleared.numerator)
    rw [← he, hy, Int.cast_mul, mul_comm]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BranchingHistoryReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical

namespace BranchingWordHistory

variable {σ : Type*}

theorem wordFormula_value (word : List σ) (env : σ → HistoryFormula σ)
    (a : σ → ℚ) (x : σ → ℤ) (he : ∀ i, (env i).value a = x i) :
    (HistoryFormula.listProduct (word.map env)).value a = ((word.map x).prod : ℚ) := by
  rw [HistoryFormula.value_listProduct, List.map_map]
  simp only [Function.comp_def]
  have hmap : word.map (fun i => (env i).value a) = word.map (fun i => (x i : ℚ)) := by
    apply List.map_congr_left
    intro i _
    exact he i
  rw [hmap]
  clear hmap
  induction word with
  | nil => simp
  | cons i word ih => simpa only [List.map_cons, List.prod_cons, Int.cast_mul] using congrArg (fun z => (x i : ℚ) * z) ih

end BranchingWordHistory
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

theorem wordTransferStep_numerator {σ : Type u} (d : WordTransferNode σ)
    (s v w : ℤ) (hs : s ≠ 0) (x : σ → ℕ) :
    (wordTransferStep d s v w hs).numerator (fun i => (x i : ℤ)) =
      v * ((d.right.map x).prod : ℤ) - w * ((d.left.map x).prod : ℤ) := by
  have hcast (word : List σ) : (word.map (fun i => (x i : ℤ))).prod = ((word.map x).prod : ℤ) := by
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
  simp only [HistoryPivotStep.numerator, wordTransferStep, hcast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Fourier factors and polynomial budgets of a concrete word history -/

namespace Ostmann

open scoped SchwartzMap FourierTransform ComplexConjugate Classical

/-- Rational reconstruction and the real polynomial specialization agree,
including away from the integral support. -/
theorem HistoryFormula.realValue_ratCast {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) :
    F.realValue x = (F.value (fun i => (x i : ℚ)) : ℝ) := by
  have hr : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℝ) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) F.cleared.numerator := by
    simpa [Int.castRingHom] using
      MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℝ) F.cleared.numerator
  have hq : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℚ) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.cleared.numerator := by
    simpa [Int.castRingHom] using
      MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.cleared.numerator
  simp only [realValue, value, ClearedHistoryValue.eval, ← hr, ← hq,
    Rat.cast_div, Rat.cast_intCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact polynomial support of one original arithmetic transfer node -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.smallDivisionTest_of_value {σ : Type*}
    (F : HistoryFormula σ) (x : σ → ℤ) (y : ℤ)
    (hy : F.value (fun i => (x i : ℚ)) = y) (m : ℕ) :
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator)
      F.cleared.denominator m ↔ IsUnit (y : ZMod m) := by
  have he := F.cleared.integer_value_cleared x y hy
  simp only [smallDivisionTest, he, dvd_mul_right, true_and,
    Int.mul_ediv_cancel_left _ F.cleared.denominator_ne_zero]

theorem HistoryFormula.smallDivisionTest_iff {σ : Type*}
    (F : HistoryFormula σ) (x : σ → ℤ) (m : ℕ) :
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator)
      F.cleared.denominator m ↔
      ∃ y : ℤ, F.value (fun i => (x i : ℚ)) = y ∧ IsUnit (y : ZMod m) := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (F.integralAt_iff x).mpr h.1
    exact ⟨y, hy, (F.smallDivisionTest_of_value x y hy m).mp h⟩
  · rintro ⟨y, hy, hu⟩
    exact (F.smallDivisionTest_of_value x y hy m).mpr hu

/-- All original node conditions are represented: both coprimality tests,
integrality, positive bounded pivot, child-frequency bounds and strict gap. -/
theorem wordTransferGuard_iff {σ : Type*} {n : ℕ} (d : WordTransferNode σ)
    (l r : WordTransferTemplate σ n) (s v w : ℤ) (hs : s ≠ 0)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (wordTransferGuard d s v w hs env).ValidAt a ↔
      ∃ P, ValidTransferNode (wordTransferSystem σ)
        ((WordTransferTemplate.node d l r).state x) s v w P := by
  let step := wordTransferStep d s v w hs
  let f := step.formula.bind env
  let g := HistoryFormula.listProduct (d.right.map env)
  let R := (d.right.map x).prod
  let L := (d.left.map x).prod
  have hcast (word : List σ) : (word.map (fun i => (x i : ℤ))).prod = ((word.map x).prod : ℤ) := by
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
  have hright : g.value (fun j => (a j : ℚ)) = (R : ℤ) := by
    have hh := BranchingWordHistory.wordFormula_value d.right env (fun j => (a j : ℚ))
      (fun i => (x i : ℤ)) (by intro i; simpa only [Int.cast_natCast] using henv i)
    have hc : (d.right.map (fun i => (x i : ℤ))).prod = (R : ℤ) := hcast d.right
    exact hh.trans (congrArg (fun z : ℤ => (z : ℚ)) hc)
  have hrightR : g.realValue a = (R : ℝ) := by
    rw [HistoryFormula.realValue_ratCast, hright, Rat.cast_intCast, Int.cast_natCast]
  have hf : f.value (fun j => (a j : ℚ)) = ((v * (R : ℤ) - w * (L : ℤ) : ℤ) : ℚ) / s := by
    rw [HistoryFormula.value_bind]
    have he : (fun i => (env i).value (fun j => (a j : ℚ))) = fun i => ((x i : ℤ) : ℚ) := by
      funext i; simpa only [Int.cast_natCast] using henv i
    rw [he, HistoryPivotStep.formula_value, wordTransferStep_numerator]
    rfl
  have hroot : IsUnit ((R : ℤ) : ZMod s.natAbs) ↔ IsCoprime s (R : ℤ) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.natCast_natAbs, IsCoprime.abs_left_iff]
  change (smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) a f.cleared.numerator) f.cleared.denominator w.natAbs ∧
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) a g.cleared.numerator) g.cleared.denominator s.natAbs ∧
    1 ≤ f.realValue a ∧ f.realValue a ≤ d.pivotBound ∧
    (2 * d.pivotBound * d.childBound : ℕ) < g.realValue a ∧
    v.natAbs ≤ d.childBound ∧ w.natAbs ≤ d.childBound) ↔ _
  rw [f.smallDivisionTest_iff, g.smallDivisionTest_of_value a (R : ℤ) hright,
    hrightR, hroot]
  constructor
  · rintro ⟨⟨Y, hY, hunit⟩, hcop, hlo, hhi, hgap, hv, hw⟩
    have hreal : f.realValue a = (Y : ℝ) := by
      rw [HistoryFormula.realValue_ratCast, hY, Rat.cast_intCast]
    rw [hreal] at hlo hhi
    have hY0 : 0 ≤ Y := by exact_mod_cast (show (0 : ℝ) ≤ Y by linarith)
    let P := Y.toNat
    have hPY : (P : ℤ) = Y := Int.toNat_of_nonneg hY0
    have hrel : v * (R : ℤ) - w * (L : ℤ) = s * P := by
      have he := (div_eq_iff (Int.cast_ne_zero.mpr hs)).mp (hf.symm.trans hY)
      have hi : v * (R : ℤ) - w * (L : ℤ) = Y * s := by exact_mod_cast he
      rw [hi, hPY, mul_comm]
    refine ⟨P, ⟨hs, hcop, hrel, ?_, ?_, hv, hw, ?_, ?_⟩⟩
    · have : (1 : ℤ) ≤ P := by rw [hPY]; exact_mod_cast hlo
      omega
    · have : (P : ℤ) ≤ d.pivotBound := by rw [hPY]; exact_mod_cast hhi
      exact_mod_cast this
    · exact_mod_cast hgap
    · have hu : IsUnit (P : ZMod w.natAbs) := by
        simpa only [← hPY, Int.cast_natCast] using hunit
      exact (ZMod.isUnit_iff_coprime P w.natAbs).mp hu
  · rintro ⟨P, hp⟩
    have hvalue : f.value (fun j => (a j : ℚ)) = (P : ℤ) := by
      have he : v * (R : ℤ) - w * (L : ℤ) = s * P := hp.relation
      rw [hf, he]
      push_cast
      exact mul_div_cancel_left₀ (P : ℚ) (Int.cast_ne_zero.mpr hs)
    have hreal : f.realValue a = (P : ℝ) := by
      rw [HistoryFormula.realValue_ratCast, hvalue, Rat.cast_intCast, Int.cast_natCast]
    refine ⟨⟨(P : ℤ), hvalue, ?_⟩, hp.root_unit, ?_, ?_, ?_, hp.left_bound, hp.right_bound⟩
    · simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime P w.natAbs).mpr hp.pivot_unit
    · rw [hreal]; exact_mod_cast hp.pivot_pos
    · rw [hreal]; exact_mod_cast hp.pivot_bound
    · exact_mod_cast hp.range_gap

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuardPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact one-variable polynomial form of each branching node guard -/

namespace Ostmann

open scoped Classical

theorem WordTransferGuard.gap_iff {σ : Type*} (g : WordTransferGuard σ) (x : σ → ℤ)
    (h : g.residueAt x) :
    ((2 * g.pivotBound * g.childBound : ℕ) : ℝ) < g.rightProduct.realValue x ↔
      ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ) ≤ g.rightProduct.realValue x := by
  obtain ⟨y, hy, _⟩ := (g.rightProduct.smallDivisionTest_iff x g.root.natAbs).mp h.2
  have he : g.rightProduct.realValue x = (y : ℝ) := by
    rw [HistoryFormula.realValue_ratCast, hy, Rat.cast_intCast]
  rw [he]
  constructor
  · intro h
    have hi : ((2 * g.pivotBound * g.childBound : ℕ) : ℤ) < y := by exact_mod_cast h
    have hj : ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℤ) ≤ y := by omega
    exact_mod_cast hj
  · intro h
    have hi : ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℤ) ≤ y := by exact_mod_cast h
    have hj : ((2 * g.pivotBound * g.childBound : ℕ) : ℤ) < y := by omega
    exact_mod_cast hj

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cleared line bounds for the source-ordered moving giant histories -/

namespace Ostmann
namespace PolynomialGiantRows

variable {σ : Type*}

theorem denominator_movingReverse (T : PolynomialGiantRows σ) (left : Bool)
    (v w u : MvPolynomial σ ℤ) :
    (T.movingReverse left v w u).denominator = T.denominator * u := by
  cases left <;> rfl

end PolynomialGiantRows

theorem movingPolynomialAncestors_denominator {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (φ : MvPolynomial σ ℤ →+* K)
    (h : ∀ s ∈ steps, φ s.u ≠ 0) :
    φ (movingPolynomialAncestors steps).denominator ≠ 0 := by
  induction steps with
  | nil => simp [movingPolynomialAncestors, PolynomialGiantRows.identity]
  | cons s steps ih =>
    rw [movingPolynomialAncestors, PolynomialGiantRows.denominator_movingReverse, map_mul]
    exact mul_ne_zero (ih fun t ht => h t (by simp [ht])) (h s (by simp))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual slot products in the moving-giant line polynomials

Lists retain multiplicities: an ancestral compensation prime may occur in
several descendant regular products. No squarefree polynomial is substituted.
-/

namespace Ostmann
open scoped BigOperators Classical

theorem movingSlotProduct_eval {σ R : Type*} [CommRing R]
    (f : ℤ →+* R) (x : σ → R) (slots : List σ) :
    MvPolynomial.eval₂Hom f x (movingSlotProduct slots) = (slots.map x).prod := by
  induction slots with
  | nil => simp [movingSlotProduct]
  | cons i slots ih => simpa [movingSlotProduct] using congrArg (x i * ·) ih

theorem movingSlotCoefficient_eval {σ R : Type*} [CommRing R]
    (f : ℤ →+* R) (x : σ → R) (s : ℤ) (slots : List σ) :
    MvPolynomial.eval₂Hom f x (movingSlotCoefficient s slots) =
      f s * (slots.map x).prod := by
  simp only [movingSlotCoefficient, map_mul, MvPolynomial.eval₂Hom_C,
    movingSlotProduct_eval]

theorem movingSlotCoefficient_ne_zero {σ K : Type*} [Field K]
    (x : σ → K) (s : ℤ) (slots : List σ)
    (hs : (s : K) ≠ 0) (hx : ∀ i ∈ slots, x i ≠ 0) :
    MvPolynomial.eval₂Hom (Int.castRingHom K) x (movingSlotCoefficient s slots) ≠ 0 := by
  rw [movingSlotCoefficient_eval]
  apply mul_ne_zero hs
  induction slots with
  | nil => simp
  | cons i slots ih =>
    exact mul_ne_zero (hx i (by simp)) (ih fun j hj => hx j (by simp [hj]))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotOccurrences
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual occurrence paths and absence of their compensation type -/

namespace Ostmann
open scoped Classical

/-- The current compensation type is strictly below every variable in the
current numerator and all its ancestor denominators. This holds for every
occurrence simultaneously, including repeated occurrences of one sample. -/
theorem MovingSlotData.occurrence_bounds {σ : Type*} (tier : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hT : T.Levels tier) :
    ∀ o ∈ T.occurrences, 0 < o.level ∧ o.level + o.path.length ≤ n ∧ o.AvoidsBelow tier := by
  induction T with
  | leaf s regular => simp [occurrences]
  | @node n s CL CR u left right ihL ihR =>
    intro o ho
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      refine ⟨by change 0 < n + 1; omega, by change n + 1 + 0 ≤ n + 1; omega, ?_⟩
      exact ⟨by simp, hT.1, hT.2.1⟩
    · have hl := ihL hT.2.2.2.1
      have hr := ihR hT.2.2.2.2
      rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨hp, hlen, ha, hb, hc⟩ := hl o' ho'
        refine ⟨hp, ?_, ?_, hb, hc⟩
        · simpa only [MovingSlotOccurrence.extend, List.length_append, List.length_singleton] using
            (show o'.level + (o'.path.length + 1) ≤ n + 1 by omega)
        · intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact ha t ht
          · have he := List.mem_singleton.mp ht
            subst t
            refine ⟨?_, ?_, ?_⟩
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.1 i hi)
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.2.1 i hi)
            · intro i hi
              change o'.level ≤ tier i
              rw [hT.2.2.1 i hi]
              omega
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨hp, hlen, ha, hb, hc⟩ := hr o' ho'
        refine ⟨hp, ?_, ?_, hb, hc⟩
        · simpa only [MovingSlotOccurrence.extend, List.length_append, List.length_singleton] using
            (show o'.level + (o'.path.length + 1) ≤ n + 1 by omega)
        · intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact ha t ht
          · have he := List.mem_singleton.mp ht
            subst t
            refine ⟨?_, ?_, ?_⟩
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.1 i hi)
            · intro i hi
              exact (show o'.level ≤ n + 1 by omega).trans (hT.2.1 i hi)
            · intro i hi
              change o'.level ≤ tier i
              rw [hT.2.2.1 i hi]
              omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotRealization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer realization of the source-ordered slot rows -/

namespace Ostmann
open scoped BigOperators Classical

namespace MovingSlotReversal

theorem coefficient_nat_eval {σ K : Type*} [CommRing K]
    (value : σ → ℕ) (s : ℤ) (slots : List σ) :
    MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i => (value i : K))
      (movingSlotCoefficient s slots) = (s : K) * (naturalProduct value slots : K) := by
  rw [movingSlotCoefficient_eval]
  congr 1
  induction slots with
  | nil => simp [naturalProduct]
  | cons i slots ih =>
    simpa only [List.map_cons, List.prod_cons, naturalProduct, Nat.cast_mul] using
      (congrArg ((value i : K) * ·) ih)

end MovingSlotReversal

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOccurrenceIntegrality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every occurrence follows the actual reconstructed integer path -/

namespace Ostmann
open scoped Classical

theorem movingSlotNaturalPath_append {σ : Type*} (value : σ → ℕ)
    (a b : List (MovingSlotReversal σ)) (pair : ℕ × ℕ) :
    movingSlotNaturalPath value (a ++ b) pair =
      movingSlotNaturalPath value a (movingSlotNaturalPath value b pair) := by
  induction a with
  | nil => rfl
  | cons s a ih => simp only [List.cons_append, movingSlotNaturalPath, ih]

theorem movingSlotPathIntegral_append {σ : Type*} (value : σ → ℕ)
    (a b : List (MovingSlotReversal σ)) (pair : ℕ × ℕ) :
    MovingSlotPathIntegral value (a ++ b) pair ↔
      MovingSlotPathIntegral value b pair ∧
        MovingSlotPathIntegral value a (movingSlotNaturalPath value b pair) := by
  induction a with
  | nil => simp [MovingSlotPathIntegral]
  | cons s a ih =>
    simp only [List.cons_append, MovingSlotPathIntegral, movingSlotNaturalPath_append, ih, and_assoc]

/-- The integral support at a tree yields all the local integer equalities
used in the polynomial line interpretation. This is constructive for every
listed occurrence, including both child orders. -/
theorem MovingSlotData.occurrence_integral {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ) (hT : T.Integral value XL XR) :
    ∀ o ∈ T.occurrences,
      MovingSlotPathIntegral value o.path (XL, XR) ∧
      o.current.IntegralAt value (movingSlotNaturalPath value o.path (XL, XR)) := by
  induction T generalizing XL XR with
  | leaf s regular => simp [occurrences]
  | @node n s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right
    let p := (step false).naturalPivot value XL XR
    have hroot : (step false).IntegralAt value (XL, XR) := hT.1
    have htrue : (step true).IntegralAt value (XL, XR) := hroot
    have hleft := ihL p XL hT.2.1
    have hright := ihR p XR hT.2.2
    intro o ho
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      exact ⟨trivial, hroot⟩
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨hp, hc⟩ := hleft o' ho'
        have hpair : movingSlotNaturalPath value [step true] (XL, XR) = (p, XL) := rfl
        constructor
        · change MovingSlotPathIntegral value (o'.path ++ [step true]) (XL, XR)
          rw [movingSlotPathIntegral_append, hpair]
          exact ⟨⟨trivial, htrue⟩, hp⟩
        · change o'.current.IntegralAt value (movingSlotNaturalPath value (o'.path ++ [step true]) (XL, XR))
          rw [movingSlotNaturalPath_append, hpair]
          exact hc
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨hp, hc⟩ := hright o' ho'
        have hpair : movingSlotNaturalPath value [step false] (XL, XR) = (p, XR) := rfl
        constructor
        · change MovingSlotPathIntegral value (o'.path ++ [step false]) (XL, XR)
          rw [movingSlotPathIntegral_append, hpair]
          exact ⟨⟨trivial, hroot⟩, hp⟩
        · change o'.current.IntegralAt value (movingSlotNaturalPath value (o'.path ++ [step false]) (XL, XR))
          rw [movingSlotNaturalPath_append, hpair]
          exact hc

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

theorem MovingSlotData.occurrence_frequencies {σ : Type*} (P : ℤ → Prop) {n : ℕ}
    (T : MovingSlotData σ n) (hT : T.Frequencies P) :
    ∀ o ∈ T.occurrences, o.current.Frequencies P ∧ ∀ s ∈ o.path, s.Frequencies P := by
  induction T with
  | leaf => simp [occurrences]
  | @node n s CL CR u left right ihL ihR =>
    intro o ho
    have hb (b : Bool) : (step s CL CR u left right b).Frequencies P :=
      ⟨hT.2.1.root, hT.2.2.root, hT.1⟩
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      exact ⟨hb false, by simp⟩
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have h := ihL hT.2.1 o' ho'
        refine ⟨h.1, ?_⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact h.2 t ht
        · simpa only [List.mem_singleton.mp ht] using hb true
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have h := ihR hT.2.2 o' ho'
        refine ⟨h.1, ?_⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact h.2 t ht
        · simpa only [List.mem_singleton.mp ht] using hb false

/-- The current compensation primes can repeat within their equality pattern.
Only their disjointness from the earlier coefficient types is used here. -/
theorem MovingSlotData.occurrence_units {σ : Type*} {q : ℕ} [Fact q.Prime]
    (tier : σ → ℕ) (value : σ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hfreq : T.Frequencies (fun s => (s : ZMod q) ≠ 0))
    (o : MovingSlotOccurrence σ) (ho : o ∈ T.occurrences)
    (hcop : ∀ i, o.level ≤ tier i → (value i).Coprime q) :
    (∀ s ∈ o.path,
      MovingSlotReversal.naturalReduction q value s.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value s.polynomial.w ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value s.polynomial.u ≠ 0) ∧
    MovingSlotReversal.naturalReduction q value o.current.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value o.current.polynomial.w ≠ 0 := by
  have hl := (T.occurrence_bounds tier hlevels o ho).2.2
  have hf := T.occurrence_frequencies _ hfreq o ho
  have hc (s : ℤ) (slots : List σ) (hs : (s : ZMod q) ≠ 0)
      (hslots : ∀ i ∈ slots, o.level ≤ tier i) :
      MovingSlotReversal.naturalReduction q value (movingSlotCoefficient s slots) ≠ 0 := by
    simpa only [MovingSlotReversal.naturalReduction] using
      movingSlotCoefficient_ne_zero (fun i => (value i : ZMod q)) s slots hs
        (fun i hi => ((ZMod.isUnit_iff_coprime _ _).mpr (hcop i (hslots i hi))).ne_zero)
  refine ⟨?_, hc _ _ hf.1.1 hl.2.2, hc _ _ hf.1.2.1 hl.2.1⟩
  intro s hs
  exact ⟨hc _ _ (hf.2 s hs).1 (hl.1 s hs).2.1,
    hc _ _ (hf.2 s hs).2.1 (hl.1 s hs).1,
    hc _ _ (hf.2 s hs).2.2 (hl.1 s hs).2.2⟩

/-- Disjoint prime types discharge all denominator and nonzero-row conditions
at every occurrence of the selected representative. -/
theorem MovingSlotData.occurrence_units_of_prime_types {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (o : MovingSlotOccurrence σ) (ho : o ∈ T.occurrences) (rep : σ)
    (hrep : tier rep < o.level)
    (hfreq : T.Frequencies (fun s => (s : ZMod (value rep)) ≠ 0)) :
    (∀ s ∈ o.path,
      MovingSlotReversal.naturalReduction (value rep) value s.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction (value rep) value s.polynomial.w ≠ 0 ∧
      MovingSlotReversal.naturalReduction (value rep) value s.polynomial.u ≠ 0) ∧
    MovingSlotReversal.naturalReduction (value rep) value o.current.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction (value rep) value o.current.polynomial.w ≠ 0 := by
  let : Fact (value rep).Prime := ⟨hprime rep⟩
  apply T.occurrence_units tier value hlevels hfreq o ho
  intro i hi
  exact (Nat.coprime_primes (hprime i) (hprime rep)).mpr
    (hdisjoint i rep (by omega))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingClearedRows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cleared rows before reduction modulo prime squares

The row identities hold over the integers before any division or reduction.
This permits the same occurrence line to be used modulo a prime square.
-/

namespace Ostmann
open scoped Classical

namespace PolynomialGiantRows

theorem cleared_movingReverse {σ R : Type*} [CommRing R]
    (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* R)
    (left : Bool) (v w u : MvPolynomial σ ℤ) (x y L H p : R)
    (hL : φ T.rows.a * x + φ T.rows.b * y = φ T.denominator * L)
    (hH : φ T.rows.c * x + φ T.rows.d * y = φ T.denominator * H)
    (hp : φ v * H - φ w * L = φ u * p) :
    let S := T.movingReverse left v w u
    φ S.rows.a * x + φ S.rows.b * y = φ S.denominator * p ∧
      φ S.rows.c * x + φ S.rows.d * y =
        φ S.denominator * (if left then L else H) := by
  have hnew : φ (v * T.rows.c - w * T.rows.a) * x +
      φ (v * T.rows.d - w * T.rows.b) * y = φ (T.denominator * u) * p := by
    simp only [map_sub, map_mul]
    linear_combination φ v * hH - φ w * hL + φ T.denominator * hp
  have hkeepL : φ (u * T.rows.a) * x + φ (u * T.rows.b) * y =
      φ (T.denominator * u) * L := by
    simp only [map_mul]
    linear_combination φ u * hL
  have hkeepH : φ (u * T.rows.c) * x + φ (u * T.rows.d) * y =
      φ (T.denominator * u) * H := by
    simp only [map_mul]
    linear_combination φ u * hH
  cases left
  · exact ⟨hnew, hkeepH⟩
  · exact ⟨hnew, hkeepL⟩

end PolynomialGiantRows

/-- The actual natural path multiplied by the cleared denominator equals
its polynomial rows over any ring, in particular over `ℤ` and `ZMod (p²)`. -/
theorem movingSlotNaturalPath_cleared {σ R : Type*} [CommRing R]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ)) (pair : ℕ × ℕ)
    (hvalid : MovingSlotPathIntegral value path pair) :
    let φ := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => (value i : R))
    let T := movingPolynomialAncestors (path.map MovingSlotReversal.polynomial)
    let out := movingSlotNaturalPath value path pair
    φ T.rows.a * (pair.1 : R) + φ T.rows.b * (pair.2 : R) =
        φ T.denominator * (out.1 : R) ∧
      φ T.rows.c * (pair.1 : R) + φ T.rows.d * (pair.2 : R) =
        φ T.denominator * (out.2 : R) := by
  let φ := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => (value i : R))
  induction path with
  | nil => simp [movingPolynomialAncestors, PolynomialGiantRows.identity,
      GiantRows.identity, movingSlotNaturalPath]
  | cons s path ih =>
    let out := movingSlotNaturalPath value path pair
    have he : φ s.polynomial.v * (out.2 : R) - φ s.polynomial.w * (out.1 : R) =
        φ s.polynomial.u * (s.naturalPivot value out.1 out.2 : R) := by
      have hc := congrArg (fun z : ℤ => (z : R)) hvalid.2.2
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at hc
      simp only [φ, MovingSlotReversal.polynomial, MovingSlotReversal.coefficient_nat_eval]
      first | (convert hc using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hc.trans (le_of_eq (by ring)))
    have h := PolynomialGiantRows.cleared_movingReverse
      (movingPolynomialAncestors (path.map MovingSlotReversal.polynomial)) φ
      s.left s.polynomial.v s.polynomial.w s.polynomial.u
      (pair.1 : R) (pair.2 : R) (out.1 : R) (out.2 : R)
      (s.naturalPivot value out.1 out.2 : R) (ih hvalid.1).1 (ih hvalid.1).2 he
    cases hleft : s.left <;>
      simpa only [List.map_cons, movingPolynomialAncestors, movingSlotNaturalPath,
        MovingSlotReversal.naturalStep, MovingSlotReversal.polynomial, hleft, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, out] using h

/-- The single cleared line is the exact current numerator times the
ancestor denominator. No unit or primality hypotheses enter this identity. -/
theorem movingSlotLine_cleared_numerator {σ R : Type*} [CommRing R]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (XL XR : ℕ)
    (hvalid : MovingSlotPathIntegral value path (XL, XR)) :
    let φ := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => (value i : R))
    let pair := movingSlotNaturalPath value path (XL, XR)
    φ (movingSlotLine path current).a * (XL : R) +
      φ (movingSlotLine path current).b * (XR : R) =
        φ (movingSlotLine path current).denominator *
          ((current.leftFrequency : R) *
              ((pair.2 * MovingSlotReversal.naturalProduct value current.rightSlots : ℕ) : R) -
            (current.rightFrequency : R) *
              ((pair.1 * MovingSlotReversal.naturalProduct value current.leftSlots : ℕ) : R)) := by
  let φ := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => (value i : R))
  have h := movingSlotNaturalPath_cleared (R := R) value path (XL, XR) hvalid
  change φ _ * (XL : R) + φ _ * (XR : R) = _
  simp only [movingSlotLine, movingHistoryLine, PolynomialGiantRows.numeratorLine,
    map_sub, map_mul]
  have he : φ current.polynomial.v *
      ((movingSlotNaturalPath value path (XL, XR)).2 : R) -
      φ current.polynomial.w * ((movingSlotNaturalPath value path (XL, XR)).1 : R) =
      (current.leftFrequency : R) *
        (((movingSlotNaturalPath value path (XL, XR)).2 *
          MovingSlotReversal.naturalProduct value current.rightSlots : ℕ) : R) -
      (current.rightFrequency : R) *
        (((movingSlotNaturalPath value path (XL, XR)).1 *
          MovingSlotReversal.naturalProduct value current.leftSlots : ℕ) : R) := by
    simp only [φ, MovingSlotReversal.polynomial, MovingSlotReversal.coefficient_nat_eval,
      Nat.cast_mul]
    ring
  rw [← he]
  linear_combination φ current.polynomial.v * h.2 - φ current.polynomial.w * h.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSquareLines
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-square exclusions for the actual moving occurrence lines -/

namespace Ostmann
open scoped BigOperators Classical

theorem movingSlotLine_square_denominator_unit {σ : Type*} {p : ℕ} [Fact p.Prime]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ)) (current : MovingSlotReversal σ)
    (hu : ∀ s ∈ path, MovingSlotReversal.naturalReduction p value s.polynomial.u ≠ 0) :
    IsUnit (MovingSlotReversal.naturalReduction (p ^ 2) value
      (movingSlotLine path current).denominator) := by
  apply (isUnit_square_iff _).mpr
  rw [naturalReduction_square]
  apply movingPolynomialAncestors_denominator
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact hu t ht

/-- The exact numerator test modulo p² is the cleared line test at the two
original giants. Only ancestor denominators need to be units. -/
theorem movingSlotLine_square_zero_iff {σ : Type*} {p : ℕ} [Fact p.Prime]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (XL XR : ℕ)
    (hvalid : MovingSlotPathIntegral value path (XL, XR))
    (hu : ∀ s ∈ path, MovingSlotReversal.naturalReduction p value s.polynomial.u ≠ 0) :
    let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
    let pair := movingSlotNaturalPath value path (XL, XR)
    φ (movingSlotLine path current).a * (XL : ZMod (p ^ 2)) +
        φ (movingSlotLine path current).b * (XR : ZMod (p ^ 2)) = 0 ↔
      (p : ℤ) ^ 2 ∣
        current.leftFrequency *
            ((pair.2 * MovingSlotReversal.naturalProduct value current.rightSlots : ℕ) : ℤ) -
          current.rightFrequency *
            ((pair.1 * MovingSlotReversal.naturalProduct value current.leftSlots : ℕ) : ℤ) := by
  let N : ℤ := current.leftFrequency *
    (((movingSlotNaturalPath value path (XL, XR)).2 *
      MovingSlotReversal.naturalProduct value current.rightSlots : ℕ) : ℤ) -
    current.rightFrequency *
    (((movingSlotNaturalPath value path (XL, XR)).1 *
      MovingSlotReversal.naturalProduct value current.leftSlots : ℕ) : ℤ)
  have he : MovingSlotReversal.naturalReduction (p ^ 2) value (movingSlotLine path current).a *
        (XL : ZMod (p ^ 2)) +
      MovingSlotReversal.naturalReduction (p ^ 2) value (movingSlotLine path current).b * (XR : ZMod (p ^ 2)) =
      MovingSlotReversal.naturalReduction (p ^ 2) value
        (movingSlotLine path current).denominator * (N : ZMod (p ^ 2)) := by
    simpa only [MovingSlotReversal.naturalReduction, N, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast] using
      movingSlotLine_cleared_numerator (R := ZMod (p ^ 2)) value path current XL XR hvalid
  change _ = 0 ↔ (p : ℤ) ^ 2 ∣ N
  rw [he, (movingSlotLine_square_denominator_unit value path current hu).mul_right_eq_zero]
  convert ZMod.intCast_zmod_eq_zero_iff_dvd N (p ^ 2) using 1
  all_goals try with_reducible_and_instances rfl
  norm_cast

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

/-- Nonzero original recursive coefficients force exactly the integral support
of the concrete moving-giant sampler. This does not assign any prime law to
its reconstructed integer pivot. -/
theorem movingSlotWeight_nonzero_integral {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (leaf : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) leaf
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t ≠ 0) :
    T.Integral value XL XR := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR with
  | leaf s regular => trivial
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    have hvalid : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P := by
      by_contra h
      apply hw
      change recursiveTransferWeight sys leaf cutoff (n + 1) x t = 0
      simp only [recursiveTransferWeight, P, h, ite_false, if_false]
    have hnode := recursiveTransferWeight_node sys leaf cutoff n x t P hvalid
    have hcut : cutoff x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ≠ 0 := by
      intro h
      apply hw
      rw [hnode, h, Complex.ofReal_zero, zero_mul, zero_mul]
    have hdiv : 0 < MovingSlotReversal.naturalProduct value u ∧
        MovingSlotReversal.naturalProduct value u ∣ P := by
      by_contra h
      apply hcut
      change (if 0 < MovingSlotReversal.naturalProduct value u ∧
        MovingSlotReversal.naturalProduct value u ∣ P then _ else 0) = 0
      exact ite_eq_right h
    let p := P / MovingSlotReversal.naturalProduct value u
    have hP : P = MovingSlotReversal.naturalProduct value u * p := by
      exact (Nat.mul_div_cancel' hdiv.2).symm
    have hp : 0 < p := by
      by_contra hp
      have hz : p = 0 := Nat.eq_zero_of_not_pos hp
      have := hvalid.pivot_pos
      rw [hP, hz, Nat.mul_zero] at this
      omega
    have hL : recursiveTransferWeight sys leaf cutoff n
        ⟨n, left, p, XL⟩ t.2.1 ≠ 0 := by
      intro h
      apply hw
      rw [hnode]
      change (cutoff x t.1 _ _ : ℂ) *
        recursiveTransferWeight sys leaf cutoff n ⟨n, left, p, XL⟩ t.2.1 * _ = 0
      rw [h, mul_zero, zero_mul]
    have hR : recursiveTransferWeight sys leaf cutoff n
        ⟨n, right, p, XR⟩ t.2.2 ≠ 0 := by
      intro h
      apply hw
      rw [hnode]
      change _ * star (recursiveTransferWeight sys leaf cutoff n ⟨n, right, p, XR⟩ t.2.2) = 0
      rw [h, star_zero, mul_zero]
    have hrel : left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
        right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ) =
        s * ((MovingSlotReversal.naturalProduct value u * p : ℕ) : ℤ) := by
      simpa only [sys, movingSlotSystem, MovingSlotState.leftProduct, MovingSlotState.rightProduct,
        x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root, hP, Int.cast_natCast] using hvalid.relation
    have hnat : (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR = p := by
      unfold MovingSlotReversal.naturalPivot movingGiantPivot
      simp only [MovingSlotData.step, Nat.mul_one]
      rw [reconstructedPivot_of_eq _ _ (by simpa only [← hT.1] using hvalid.root_ne_zero)
        (MovingSlotReversal.naturalProduct value u * p) hrel]
      exact Nat.mul_div_cancel_left p hdiv.1
    change (_ ∧ _ ∧ _)
    refine ⟨?_, ?_, ?_⟩
    · change 0 < (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR ∧ _
      constructor
      · exact hnat.symm ▸ hp
      · change left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
          right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ) =
          s * ((MovingSlotReversal.naturalProduct value u *
            (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR : ℕ) : ℤ)
        rw [hnat]
        exact hrel
    · rw [hnat]
      exact ihL t.2.1 hT.2.1 p XL hL
    · rw [hnat]
      exact ihR t.2.2 hT.2.2 p XR hR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCoprimeDescent
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coprimality inherited by an actual moving reversal

These are the support reductions in Section 8.1: the numerator is a unit at
all old slots, so an integral reconstructed pivot and its compensation are
already coprime to every inherited slot. Only their mutual coprimality and
the outside-prime tests remain.
-/

namespace Ostmann

/-- The compensation product and reconstructed giant inherit every old
coprimality test directly from the integer relation. -/
theorem moving_pivot_inherited_coprime (L R u p : ℕ) (s v w : ℤ)
    (hLR : L.Coprime R) (hv : IsCoprime v (L : ℤ)) (hw : IsCoprime w (R : ℤ))
    (hrel : v * R - w * L = s * ((u * p : ℕ) : ℤ)) :
    u.Coprime (L * R) ∧ p.Coprime (L * R) := by
  have hr : v * (R : ℤ) - w * L = s * (u : ℤ) * p := by
    simpa only [Nat.cast_mul, mul_assoc] using hrel
  have h := reversal_inherited_coprime v w L R s u p hLR.isCoprime hv hw hr
  constructor
  · exact Nat.isCoprime_iff_coprime.mp (by simpa only [Nat.cast_mul] using h.2)
  · exact Nat.isCoprime_iff_coprime.mp (by simpa only [Nat.cast_mul] using h.1)

private theorem pairwise_append_of_products (A B : List ℕ)
    (hA : A.Pairwise Nat.Coprime) (hB : B.Pairwise Nat.Coprime)
    (hAB : A.prod.Coprime B.prod) : (A ++ B).Pairwise Nat.Coprime := by
  apply List.pairwise_append.mpr
  refine ⟨hA, hB, ?_⟩
  intro a ha b hb
  exact (Nat.coprime_list_prod_left_iff.mp
    (Nat.coprime_list_prod_right_iff.mp hAB b hb) a ha)

private theorem coprime_products_of_pairwise_append (A B : List ℕ)
    (h : (A ++ B).Pairwise Nat.Coprime) : A.prod.Coprime B.prod := by
  have hc := (List.pairwise_append.mp h).2.2
  apply Nat.coprime_list_prod_left_iff.mpr
  intro a ha
  apply Nat.coprime_list_prod_right_iff.mpr
  intro b hb
  exact hc a ha b hb

/-- The two actual child lists have precisely one new coprimality condition:
the inserted giant must be coprime to its own compensation list. All inherited
cross-list conditions follow from the numerator equation. -/
theorem moving_children_pairwise_iff (L R U : List ℕ) (p : ℕ) (s v w : ℤ)
    (hold : (L ++ R).Pairwise Nat.Coprime)
    (hv : IsCoprime v (L.prod : ℤ)) (hw : IsCoprime w (R.prod : ℤ))
    (hrel : v * R.prod - w * L.prod = s * ((U.prod * p : ℕ) : ℤ)) :
    ((p :: (U ++ L)).Pairwise Nat.Coprime ∧ (p :: (U ++ R)).Pairwise Nat.Coprime) ↔
      U.Pairwise Nat.Coprime ∧ p.Coprime U.prod := by
  constructor
  · rintro ⟨hleft, _⟩
    obtain ⟨hpu, hUL⟩ := List.pairwise_cons.mp hleft
    refine ⟨(List.pairwise_append.mp hUL).1, Nat.coprime_list_prod_right_iff.mpr ?_⟩
    intro b hb
    exact hpu b (List.mem_append_left _ hb)
  · rintro ⟨hU, hpU⟩
    have hLR := coprime_products_of_pairwise_append L R hold
    obtain ⟨hu, hp⟩ := moving_pivot_inherited_coprime L.prod R.prod U.prod p s v w hLR hv hw hrel
    obtain ⟨hL, hR, _⟩ := List.pairwise_append.mp hold
    have child (A : List ℕ) (hA : A.Pairwise Nat.Coprime)
        (huA : U.prod.Coprime A.prod) (hpA : p.Coprime A.prod) :
        (p :: (U ++ A)).Pairwise Nat.Coprime := by
      apply List.pairwise_cons.mpr
      refine ⟨?_, pairwise_append_of_products U A hU hA huA⟩
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact Nat.coprime_list_prod_right_iff.mp hpU b hb
      · exact Nat.coprime_list_prod_right_iff.mp hpA b hb
    exact ⟨child L hL (Nat.coprime_mul_iff_right.mp hu).1 (Nat.coprime_mul_iff_right.mp hp).1,
      child R hR (Nat.coprime_mul_iff_right.mp hu).2 (Nat.coprime_mul_iff_right.mp hp).2⟩

private theorem compensation_product_squarefree (U : List ℕ)
    (hprime : ∀ b ∈ U, b.Prime) (hpair : U.Pairwise Nat.Coprime) : Squarefree U.prod := by
  induction U with
  | nil => simp
  | cons b U ih =>
    obtain ⟨hbU, hU⟩ := List.pairwise_cons.mp hpair
    have hcop : b.Coprime U.prod := Nat.coprime_list_prod_right_iff.mpr hbU
    rw [List.prod_cons, Nat.squarefree_mul hcop]
    exact ⟨(hprime b (by simp)).squarefree,
      ih (fun c hc => hprime c (List.mem_cons_of_mem _ hc)) hU⟩

/-- The own-compensation unit test is exactly the nonvanishing numerator
condition modulo the square of each distinct sampled compensation prime. -/
theorem moving_compensation_square_tests (U : List ℕ) (p : ℕ) (s : ℤ)
    (hprime : ∀ b ∈ U, b.Prime) (hpair : U.Pairwise Nat.Coprime)
    (hs : ∀ b ∈ U, ¬ b ∣ s.natAbs) :
    p.Coprime U.prod ↔ ∀ b ∈ U, ¬ (b : ℤ) ^ 2 ∣ s * ((U.prod * p : ℕ) : ℤ) := by
  have hsf := compensation_product_squarefree U hprime hpair
  have heq (b : ℕ) (hb : b ∈ U) :
      (¬ (b : ℤ) ^ 2 ∣ s * ((U.prod * p : ℕ) : ℤ)) ↔ ¬ b ∣ p := by
    have hd : ((b : ℤ) ^ 2 ∣ s * ((U.prod * p : ℕ) : ℤ)) ↔
        b ^ 2 ∣ s.natAbs * U.prod * p := by
      rw [← Nat.cast_pow, Int.natCast_dvd]
      simp only [Int.natAbs_mul, Int.natAbs_natCast, mul_assoc]
    rw [hd]
    apply reversal_square_test b s.natAbs U.prod p (hprime b hb) (hs b hb)
      (List.dvd_prod hb)
    have h := Nat.squarefree_iff_prime_squarefree.mp hsf b (hprime b hb)
    simpa only [pow_two] using h
  rw [Nat.coprime_list_prod_right_iff]
  constructor
  · intro h b hb
    exact (heq b hb).mpr ((hprime b hb).coprime_iff_not_dvd.mp (h b hb).symm)
  · intro h b hb
    exact ((hprime b hb).coprime_iff_not_dvd.mpr ((heq b hb).mp (h b hb))).symm

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

/-- Coherence is proved for the actual sampler, not supplied as a new
assumption about the original history. -/
theorem buildMovingSlotData_regular_coherent {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).RegularCoherent := by
  induction samples with
  | leaf => trivial
  | @node n samples left right ihL ihR =>
    let U := movingCompensationSlots n samples
    have hL := (buildMovingSlotData_regular_perm n t.2.1
      (appendMovingSlotLeaves n U small.1) bulk.1 left).trans
      ((flattenMovingSlots_append_perm n U small.1).append_right (flattenMovingSlots n bulk.1))
    have hR := (buildMovingSlotData_regular_perm n t.2.2
      (appendMovingSlotLeaves n U small.2) bulk.2 right).trans
      ((flattenMovingSlots_append_perm n U small.2).append_right (flattenMovingSlots n bulk.2))
    refine ⟨?_, ?_, ihL _ _ _, ihR _ _ _⟩
    · simpa only [List.append_assoc] using hL
    · simpa only [List.append_assoc] using hR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPairwiseSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing full moving-history coprimality to the new compensation tests -/

namespace Ostmann
open scoped Classical

private theorem parent_current_perm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n) (XL XR : ℕ) :
    ((.node s CL CR U left right : MovingSlotData σ (n + 1)).currentSlots value XL XR).Perm
      ((XL :: CL.map value) ++ (XR :: CR.map value)) := by
  apply List.perm_iff_count.mpr
  intro a
  simp only [MovingSlotData.currentSlots, MovingSlotData.regularSlots,
    List.map_append, List.count_cons, List.count_append]
  omega

private theorem child_current_perm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (U C : List σ) (h : T.regularSlots.Perm (U ++ C))
    (p x : ℕ) : (T.currentSlots value p x).Perm (p :: (U.map value ++ (x :: C.map value))) := by
  have hp := List.perm_iff_count.mp (h.map value)
  apply List.perm_iff_count.mpr
  intro a
  have ha := hp a
  simp only [List.map_append, List.count_append] at ha
  simp only [MovingSlotData.currentSlots, List.count_cons, List.count_append]
  omega

/-- The local equivalence is stated on the actual child states. Slot
coherence is available for every `buildMovingSlotData` by construction. -/
theorem moving_node_pairwise_iff {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n)
    (hcoh : (.node s CL CR U left right : MovingSlotData σ (n + 1)).RegularCoherent)
    (XL XR : ℕ)
    (hold : (.node s CL CR U left right : MovingSlotData σ (n + 1)).CurrentPairwise value XL XR)
    (hv : IsCoprime left.frequency (XL * MovingSlotReversal.naturalProduct value CL : ℤ))
    (hw : IsCoprime right.frequency (XR * MovingSlotReversal.naturalProduct value CR : ℤ))
    (hI : (MovingSlotData.step s CL CR U left right false).IntegralAt value (XL, XR)) :
    let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
    (left.CurrentPairwise value p XL ∧ right.CurrentPairwise value p XR) ↔
      (U.map value).Pairwise Nat.Coprime ∧ p.Coprime (MovingSlotReversal.naturalProduct value U) := by
  dsimp only
  let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
  have hp := (parent_current_perm value s CL CR U left right XL XR).pairwise_iff (R := Nat.Coprime)
    (fun h => h.symm)
  have hleft := (child_current_perm value left U CL hcoh.1 p XL).pairwise_iff (R := Nat.Coprime)
    (fun h => h.symm)
  have hright := (child_current_perm value right U CR hcoh.2.1 p XR).pairwise_iff (R := Nat.Coprime)
    (fun h => h.symm)
  have h := moving_children_pairwise_iff (XL :: CL.map value) (XR :: CR.map value)
    (U.map value) p s left.frequency right.frequency (hp.mp hold)
    (by simpa only [List.prod_cons, MovingSlotReversal.naturalProduct, Nat.cast_mul] using hv)
    (by simpa only [List.prod_cons, MovingSlotReversal.naturalProduct, Nat.cast_mul] using hw)
    (by simpa only [List.prod_cons, MovingSlotReversal.naturalProduct, MovingSlotData.step, p]
      using hI.2)
  exact (and_congr hleft hright).trans h

/-- Full pairwise coprimality down the original moving tree is equivalent
to top coprimality and the new compensation tests. Integral reconstruction
and all cross-frequency tests remain hypotheses on these exact states. -/
theorem MovingSlotData.fullPairwise_iff {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hcoh : T.RegularCoherent) (XL XR : ℕ)
    (hI : T.Integral value XL XR) (hfreq : T.CrossFrequencyUnits value XL XR) :
    T.FullPairwise value XL XR ↔ T.CurrentPairwise value XL XR ∧ T.NewCompensationUnits value XL XR := by
  induction T generalizing XL XR with
  | leaf => simp only [FullPairwise, NewCompensationUnits, and_true]
  | node s CL CR U left right ihL ihR =>
    have hL := ihL hcoh.2.2.1 _ _ hI.2.1 hfreq.2.2.1
    have hR := ihR hcoh.2.2.2 _ _ hI.2.2 hfreq.2.2.2
    change (_ ∧ _ ∧ _) ↔ _ ∧ (_ ∧ _ ∧ _)
    rw [hL, hR]
    constructor
    · rintro ⟨htop, ⟨hl, hnewL⟩, ⟨hr, hnewR⟩⟩
      exact ⟨htop, (moving_node_pairwise_iff value s CL CR U left right hcoh XL XR htop
        hfreq.1 hfreq.2.1 hI.1).mp ⟨hl, hr⟩, hnewL, hnewR⟩
    · rintro ⟨htop, hnew, hnewL, hnewR⟩
      have hc := (moving_node_pairwise_iff value s CL CR U left right hcoh XL XR htop
        hfreq.1 hfreq.2.1 hI.1).mpr hnew
      exact ⟨htop, ⟨hc.1, hnewL⟩, ⟨hc.2, hnewR⟩⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSquareSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit prime-square tests for the full moving history -/

namespace Ostmann

theorem MovingSlotData.newCompensationUnits_iff_squareTests {σ : Type*}
    (value : σ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hprime : T.CompensationPrimeData value) (XL XR : ℕ) (hI : T.Integral value XL XR) :
    T.NewCompensationUnits value XL XR ↔ T.PrimeSquareTests value XL XR := by
  induction T generalizing XL XR with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    have hs := moving_compensation_square_tests (U.map value)
      ((MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR)
      s hprime.1 hprime.2.1 hprime.2.2.1
    have he : (∀ b ∈ U.map value, ¬ (b : ℤ) ^ 2 ∣
        left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
        right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ)) ↔
      (∀ b ∈ U.map value, ¬ (b : ℤ) ^ 2 ∣ s *
        ((MovingSlotReversal.naturalProduct value U *
          (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR : ℕ) : ℤ)) := by
      have hrel := hI.1.2
      dsimp only [MovingSlotData.step] at hrel
      rw [hrel]
      rfl
    change (_ ∧ _ ∧ _) ↔ _ ∧ _ ∧ _
    rw [ihL hprime.2.2.2.1 _ _ hI.2.1, ihR hprime.2.2.2.2 _ _ hI.2.2, he]
    exact and_congr (by simpa only [MovingSlotReversal.naturalProduct, hprime.2.1, true_and] using hs)
      Iff.rfl

/-- An exact reduction of all pairwise slot tests to the top support and the
explicit numerator exclusions modulo b², for the original integral tree. -/
theorem MovingSlotData.fullPairwise_iff_squareTests {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hcoh : T.RegularCoherent)
    (hprime : T.CompensationPrimeData value) (XL XR : ℕ)
    (hI : T.Integral value XL XR) (hfreq : T.CrossFrequencyUnits value XL XR) :
    T.FullPairwise value XL XR ↔ T.CurrentPairwise value XL XR ∧ T.PrimeSquareTests value XL XR := by
  rw [T.fullPairwise_iff value hcoh XL XR hI hfreq,
    T.newCompensationUnits_iff_squareTests value hprime XL XR hI]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOccurrenceSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full square support as the actual occurrence line tests -/

namespace Ostmann
open scoped Classical

/-- All recursive exclusions are exactly the exclusions in the recorded
occurrence list, evaluated along their actual natural paths. -/
theorem MovingSlotData.squareTests_iff_occurrences {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    T.PrimeSquareTests value XL XR ↔
      ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
        ¬ (value i : ℤ) ^ 2 ∣ o.current.integerNumerator value
          (movingSlotNaturalPath value o.path (XL, XR)) := by
  induction T generalizing XL XR with
  | leaf => simp [PrimeSquareTests, occurrences]
  | @node n s CL CR U left right ihL ihR =>
    let step := MovingSlotData.step s CL CR U left right
    let p := (step false).naturalPivot value XL XR
    have hl := ihL p XL
    have hr := ihR p XR
    constructor
    · rintro ⟨hroot, hleft, hright⟩ o ho i hi
      rcases List.mem_cons.mp ho with ho | ho
      · subst o
        exact hroot (value i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      · rcases List.mem_append.mp ho with ho | ho
        · obtain ⟨o', hmem, rfl⟩ := List.mem_map.mp ho
          have h := hl.mp hleft o' hmem i hi
          simpa only [MovingSlotOccurrence.extend, movingSlotNaturalPath_append,
            movingSlotNaturalPath, MovingSlotReversal.naturalStep, p, step, MovingSlotReversal.naturalPivot,
            MovingSlotData.step, ite_true, if_true] using h
        · obtain ⟨o', hmem, rfl⟩ := List.mem_map.mp ho
          have h := hr.mp hright o' hmem i hi
          simpa only [MovingSlotOccurrence.extend, movingSlotNaturalPath_append,
            movingSlotNaturalPath, MovingSlotReversal.naturalStep, p, step, MovingSlotReversal.naturalPivot,
            MovingSlotData.step, Bool.false_eq_true, ite_false, if_false] using h
    · intro h
      refine ⟨?_, hl.mpr ?_, hr.mpr ?_⟩
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        exact h ⟨n + 1, step false, []⟩ (List.mem_cons_self) i hi
      · intro o ho i hi
        have hh := h (o.extend (step true))
          (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩))) i hi
        simpa only [MovingSlotOccurrence.extend, movingSlotNaturalPath_append,
          movingSlotNaturalPath, MovingSlotReversal.naturalStep, p, step, MovingSlotReversal.naturalPivot,
          MovingSlotData.step, ite_true, if_true] using hh
      · intro o ho i hi
        have hh := h (o.extend (step false))
          (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩))) i hi
        simpa only [MovingSlotOccurrence.extend, movingSlotNaturalPath_append,
          movingSlotNaturalPath, MovingSlotReversal.naturalStep, p, step, MovingSlotReversal.naturalPivot,
          MovingSlotData.step, Bool.false_eq_true, ite_false, if_false] using hh

/-- A current compensation slot belongs to the type immediately below the
occurrence, including when a prime represents multiple occurrences. -/
theorem MovingSlotData.occurrence_compensation_level {σ : Type*} (tier : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.Levels tier) :
    ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, tier i < o.level := by
  induction T with
  | leaf => simp [occurrences]
  | @node n s CL CR U left right ihL ihR =>
    intro o ho i hi
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      have he := hT.2.2.1 i hi
      change tier i < n + 1
      omega
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', hmem, rfl⟩ := List.mem_map.mp ho
        exact ihL hT.2.2.2.1 o' hmem i hi
      · obtain ⟨o', hmem, rfl⟩ := List.mem_map.mp ho
        exact ihR hT.2.2.2.2 o' hmem i hi

/-- The full recursive support has only linear equations at the original
pair of giants modulo the current compensation-prime squares. -/
theorem MovingSlotData.squareTests_iff_lines {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (hfreq : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR) :
    T.PrimeSquareTests value XL XR ↔
      ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
        let φ := MovingSlotReversal.naturalReduction (value i ^ 2) value
        φ (movingSlotLine o.path o.current).a * (XL : ZMod (value i ^ 2)) +
          φ (movingSlotLine o.path o.current).b * (XR : ZMod (value i ^ 2)) ≠ 0 := by
  rw [T.squareTests_iff_occurrences value XL XR]
  apply forall₂_congr
  intro o ho
  apply forall₂_congr
  intro i hi
  let : Fact (value i).Prime := ⟨hprime i⟩
  have hu := T.occurrence_units_of_prime_types tier value hprime hdisjoint hlevels
    o ho i (T.occurrence_compensation_level tier hlevels o ho i hi) (hfreq i)
  have hv := (T.occurrence_integral value XL XR hI o ho).1
  exact (not_congr (movingSlotLine_square_zero_iff value o.path o.current XL XR hv
    (fun s hs => (hu.1 s hs).2.2))).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorWeightFactorization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the spectator from the original supported coefficient -/

namespace Ostmann
open scoped Classical ComplexConjugate BigOperators

theorem recursiveTransferWeight_mul_leaf {State : Type*}
    (sys : TransferHistorySystem State) (F G : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight sys (fun σ s => F σ s * G σ s) cutoff n σ t =
      recursiveTransferWeight sys F cutoff n σ t *
        recursiveTransferWeight sys G (fun _ _ _ _ => 1) n σ t := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    simp only [recursiveTransferWeight]
    split_ifs with hv
    · rw [ih, ih]
      simp only [star_mul, Complex.ofReal_one, one_mul]
      ring
    · simp only [zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantArchimedean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual terminal moduli as quadratic functions of a top giant

Small prime values are fixed here. Every reconstructed giant is linear in the
initial pair, and each terminal modulus is a product of two such linear forms.
The identification uses the integer support equations of the original sampler.
-/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.realPivot_eq {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : ℕ)
    (hs : s.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value s.compensationSlots ≠ 0)
    (h : s.IntegralAt value (XL, XR)) :
    s.realPivot value XL XR = (s.naturalPivot value XL XR : ℝ) := by
  have he := congrArg (fun z : ℤ => (z : ℝ)) h.2
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
  unfold realPivot
  apply (div_eq_iff (mul_ne_zero (Int.cast_ne_zero.mpr hs) (Nat.cast_ne_zero.mpr hu))).mpr
  nlinarith only [he]

theorem MovingSlotReversal.pivotPolynomial_eval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : Polynomial ℝ) (z : ℝ) :
    (s.pivotPolynomial value XL XR).eval z = s.realPivot value (XL.eval z) (XR.eval z) := by
  simp only [pivotPolynomial, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    realPivot, div_eq_mul_inv]
  ring

/-- Exact agreement on integer support; no approximation or extra
real-variable realization condition is assumed. -/
theorem MovingSlotData.leafPolynomials_eval {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) {n : ℕ} (T : MovingSlotData σ n)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (hI : T.Integral value XL XR)
    (L R : Polynomial ℝ) (z : ℝ) (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ))
    (i : TreeLeafIndex n) :
    (T.leafPolynomials value L R i).eval z = (T.leafModuli value XL XR i : ℝ) := by
  induction T generalizing XL XR L R with
  | leaf s regular =>
    simp only [leafPolynomials, leafModuli, Polynomial.eval_mul, Polynomial.eval_C,
      hL, hR, Nat.cast_mul]
  | node s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    have hp : (step.pivotPolynomial value L R).eval z = (step.naturalPivot value XL XR : ℝ) := by
      rw [MovingSlotReversal.pivotPolynomial_eval, hL, hR]
      exact step.realPivot_eq value XL XR hfreq.1
        (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) hI.1
    cases i with
    | inl i => exact ihL hfreq.2.1 _ _ hI.2.1 _ _ hp hL i
    | inr i => exact ihR hfreq.2.2 _ _ hI.2.2 _ _ hp hR i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial smooth factors in the full moving-giant coefficient -/

namespace Ostmann
open scoped Classical ComplexConjugate

theorem movingPolynomialFourierTree_eq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (ψ : ℝ → ℂ) (X z : ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (hfreq : T.Frequencies (· ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR) (L R : Polynomial ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    movingPolynomialFourierTree value ψ X z T L R = movingFourierTree value ψ X T XL XR := by
  induction T generalizing XL XR L R with
  | leaf s regular =>
    simp only [movingPolynomialFourierTree, movingFourierTree, Polynomial.eval_mul,
      Polynomial.eval_C, hL, hR, Nat.cast_mul]
  | node s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    have hp : (step.pivotPolynomial value L R).eval z = (step.naturalPivot value XL XR : ℝ) := by
      rw [MovingSlotReversal.pivotPolynomial_eval, hL, hR]
      exact step.realPivot_eq value XL XR hfreq.1
        (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) hI.1
    exact congrArg₂ (fun a b : ℂ => a * star b)
      (ihL hfreq.2.1 _ _ hI.2.1 _ _ hp hL) (ihR hfreq.2.2 _ _ hI.2.2 _ _ hp hR)

/-- The exact Fourier factorization preserves all original support terms,
including terms whose full coefficient is zero. -/
theorem movingSlotWeight_fourier {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (ψ : ℝ → ℂ) (X : ℝ) {n : ℕ}
    (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => F x s * movingFourierLeaf value ψ X x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t *
        movingFourierTree value ψ X T XL XR := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR with
  | leaf s regular =>
    have hs : s = t := hT
    simp only [recursiveTransferWeight, movingFourierLeaf, movingSlotModulus,
      movingFourierTree, hs]
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
    have hp : historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
        MovingSlotReversal.naturalProduct value u = p := by
      simp only [historyPivot, sys, movingSlotSystem,
        MovingSlotState.leftProduct, MovingSlotState.rightProduct, x,
        ← hT.1, ← hT.2.1.root, ← hT.2.2.root, p,
        MovingSlotReversal.naturalPivot, MovingSlotData.step, movingGiantPivot, Nat.mul_one]
    change recursiveTransferWeight sys _ cutoff (n + 1) x t = _
    simp only [recursiveTransferWeight]
    split_ifs
    · change (cutoff x t.1 _ _ : ℂ) *
          recursiveTransferWeight sys _ cutoff n ⟨n, left, _, XL⟩ t.2.1 *
          star (recursiveTransferWeight sys _ cutoff n ⟨n, right, _, XR⟩ t.2.2) =
        ((cutoff x t.1 _ _ : ℂ) * recursiveTransferWeight sys F cutoff n ⟨n, left, _, XL⟩ t.2.1 *
          star (recursiveTransferWeight sys F cutoff n ⟨n, right, _, XR⟩ t.2.2)) * _
      rw [hp, ihL t.2.1 hT.2.1 p XL, ihR t.2.2 hT.2.2 p XR]
      change _ = _ * (movingFourierTree value ψ X left p XL * star (movingFourierTree value ψ X right p XR))
      simp only [star_mul]
      ring
    · exact (zero_mul _).symm

/-- The polynomial smooth extension agrees with the full coefficient on
its proved integer support. No polynomial realization premise is required. -/
theorem movingSlotWeight_polynomial_fourier {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (ψ : ℝ → ℂ) (X z : ℝ) {n : ℕ}
    (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : Polynomial ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => F x s * movingFourierLeaf value ψ X x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t *
        movingPolynomialFourierTree value ψ X z T L R := by
  rw [movingSlotWeight_fourier value childBound pivotBound F extra ψ X T t hT XL XR]
  by_cases hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t = 0
  · rw [hw, zero_mul, zero_mul]
  · have hi := movingSlotWeight_nonzero_integral value childBound pivotBound F extra T t hT XL XR hw
    rw [movingPolynomialFourierTree_eq value hvalue ψ X z T hfreq XL XR hi L R hL hR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete polynomial factors in the moving Fourier history -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem movingPolynomialFourierTree_product {σ : Type*}
    (value : σ → ℕ) (ψ : ℝ → ℂ) (X z : ℝ) {n : ℕ} (T : MovingSlotData σ n)
    (L R : Polynomial ℝ) (b : Bool) :
    (∏ i : TreeLeafIndex n,
      if treeLeafTupleEquiv Bool n (transferConjugations n b) i then
        conj (normalizedFourierProfile ψ (T.leafFrequencies i)
          ((T.leafPolynomials value L R i).eval z / X))
      else normalizedFourierProfile ψ (T.leafFrequencies i)
          ((T.leafPolynomials value L R i).eval z / X)) =
      if b then conj (movingPolynomialFourierTree value ψ X z T L R)
      else movingPolynomialFourierTree value ψ X z T L R := by
  induction T generalizing L R b with
  | leaf s regular =>
    change (∏ _ : Unit, if b then conj _ else _) = _
    simp only [Fintype.prod_unique]
    rfl
  | @node n s CL CR u left right ihL ihR =>
    change (∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n, _) = _
    rw [Fintype.prod_sum_type]
    change (∏ i : TreeLeafIndex n, if treeLeafTupleEquiv Bool n (transferConjugations n b) i
        then conj _ else _) *
      (∏ i : TreeLeafIndex n, if treeLeafTupleEquiv Bool n (transferConjugations n (!b)) i
        then conj _ else _) = _
    simp only [MovingSlotData.leafFrequencies, MovingSlotData.leafPolynomials]
    rw [ihL, ihR]
    cases b
    · rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
      change star _ * _ = star (_ * star _)
      rw [star_mul, star_star]
      exact mul_comm _ _

theorem movingLeafNormalizedPolynomial_eval {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X z : ℝ) (i : TreeLeafIndex n) :
    (movingLeafNormalizedPolynomial value T L R X i).eval z =
      (T.leafPolynomials value L R i).eval z / X := by
  simp only [movingLeafNormalizedPolynomial, Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv]
  ring

theorem movingFourierPolynomialFactors_value {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (z : ℝ)
    (hrange : ∀ i, (T.leafPolynomials value L R i).eval z / X ∈ Set.Icc lo hi) :
    smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z =
      movingPolynomialFourierTree value ψ X z T L R := by
  rw [smoothPolynomialWeight]
  have he := (movingLeafIndexEquiv n).prod_comp
    (fun j => (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi j).value z)
  rw [← he]
  have ht (i : TreeLeafIndex n) :
      (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi
        (movingLeafIndexEquiv n i)).value z =
      if treeLeafTupleEquiv Bool n (transferConjugations n false) i then
        conj (normalizedFourierProfile ψ (T.leafFrequencies i)
          ((T.leafPolynomials value L R i).eval z / X))
      else normalizedFourierProfile ψ (T.leafFrequencies i)
          ((T.leafPolynomials value L R i).eval z / X) := by
    simp only [movingFourierPolynomialFactors, Equiv.symm_apply_apply]
    have hv := ClippedPolynomialFactor.value_of_mem
      (fourierPolynomialFactor (movingLeafNormalizedPolynomial value T L R X i)
        ψ (T.leafFrequencies i) lo hi hlo hhi) z
      (by simpa only [fourierPolynomialFactor, movingLeafNormalizedPolynomial_eval] using hrange i)
    have hv' : (fourierPolynomialFactor (movingLeafNormalizedPolynomial value T L R X i)
        ψ (T.leafFrequencies i) lo hi hlo hhi).value z =
        normalizedFourierProfile ψ (T.leafFrequencies i)
          ((T.leafPolynomials value L R i).eval z / X) := by
      rw [hv]
      exact congrArg (normalizedFourierProfile ψ (T.leafFrequencies i))
        (movingLeafNormalizedPolynomial_eval value T L R X z i)
    split_ifs
    · rw [ClippedPolynomialFactor.conjugate_value]
      exact congrArg conj hv'
    · exact hv'
  simp_rw [ht]
  exact movingPolynomialFourierTree_product value ψ X z T L R false

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierSupported
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The supported original coefficient is the constructed polynomial weight -/

namespace Ostmann
open scoped Classical SchwartzMap

/-- Every terminal factor of a nonzero recursive coefficient is nonzero.
This statement keeps the concrete moving giant and terminal modulus. -/
theorem movingSlotWeight_leaf_support {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (P : ℕ → ℤ → Prop)
    (hF : ∀ x s, F x s ≠ 0 → P (movingSlotModulus value x) s)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t ≠ 0) :
    ∀ i, P (T.leafModuli value XL XR i) (T.leafFrequencies i) := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR with
  | leaf s regular =>
    intro i
    have hs : s = t := hT
    subst s
    exact hF ⟨0, .leaf t regular, XL, XR⟩ t hw
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
    have hp : historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
        MovingSlotReversal.naturalProduct value u = p := by
      simp only [historyPivot, sys, movingSlotSystem, MovingSlotState.leftProduct,
        MovingSlotState.rightProduct, x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root, p,
        MovingSlotReversal.naturalPivot, MovingSlotData.step, movingGiantPivot, Nat.mul_one]
    have hvalid := recursiveTransferWeight_nonzero_valid sys F cutoff (n + 1) x t hw
    obtain ⟨Q, hQ, _, _⟩ := hvalid
    have hnode := recursiveTransferWeight_node sys F cutoff n x t Q hQ
    have hQp : Q / MovingSlotReversal.naturalProduct value u = p := by
      rw [← hQ.historyPivot_eq]
      exact hp
    have hL : recursiveTransferWeight sys F cutoff n ⟨n, left, p, XL⟩ t.2.1 ≠ 0 := by
      intro hz
      apply hw
      rw [hnode]
      change (cutoff x t.1 _ _ : ℂ) *
        recursiveTransferWeight sys F cutoff n ⟨n, left, Q / _, XL⟩ t.2.1 * _ = 0
      rw [hQp, hz, mul_zero, zero_mul]
    have hR : recursiveTransferWeight sys F cutoff n ⟨n, right, p, XR⟩ t.2.2 ≠ 0 := by
      intro hz
      apply hw
      rw [hnode]
      change _ * star (recursiveTransferWeight sys F cutoff n ⟨n, right, Q / _, XR⟩ t.2.2) = 0
      rw [hQp, hz, star_zero, mul_zero]
    intro i
    cases i with
    | inl i => exact ihL t.2.1 hT.2.1 p XL hL i
    | inr i => exact ihR t.2.2 hT.2.2 p XR hR i

/-- The original sharp terminal windows suffice for the clipped polynomial
extension. All node and prime restrictions remain in the scalar coefficient. -/
theorem moving_windowed_fourier_polynomial {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : Polynomial ℝ) (z : ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => movingWindowLeaf value X lo hi F x s * movingFourierLeaf value ψ X x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
        n ⟨n, T, XL, XR⟩ t *
        smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z := by
  rw [movingSlotWeight_polynomial_fourier value hvalue childBound pivotBound
    (movingWindowLeaf value X lo hi F) extra ψ X z T t hT hfreq XL XR L R hL hR]
  by_cases hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
      n ⟨n, T, XL, XR⟩ t = 0
  · rw [hw, zero_mul, zero_mul]
  · have hI := movingSlotWeight_nonzero_integral value childBound pivotBound
      (movingWindowLeaf value X lo hi F) extra T t hT XL XR hw
    have hr := movingSlotWeight_leaf_support value childBound pivotBound
      (movingWindowLeaf value X lo hi F) extra (fun M _ => (M : ℝ) / X ∈ Set.Icc lo hi)
      (fun x s hx => by
        by_contra hn
        exact hx (by simp only [movingWindowLeaf, ite_eq_right hn])) T t hT XL XR hw
    rw [movingFourierPolynomialFactors_value value T L R ψ X lo hi hlo hhi z]
    intro i
    rw [T.leafPolynomials_eval value hvalue hfreq XL XR hI L R z hL hR i]
    exact hr i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingNodeGuards
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial and residue tests for the actual moving-giant node -/

namespace Ostmann
open scoped Classical

/-- Identification with the original validity predicate, before any
arithmetic restriction is removed. -/
theorem movingNodeGuard_iff {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (s : ℤ) (CL CR u : List σ)
    (left right : MovingSlotData σ n) (hs : s ≠ 0) (XL XR : ℕ)
    (L R : HistoryFormula Bool) (a : Bool → ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ)) :
    (movingNodeGuard (MovingSlotReversal.naturalProduct value CL)
      (MovingSlotReversal.naturalProduct value CR) s left.frequency right.frequency hs
      (childBound (n + 1)) (pivotBound (n + 1)) L R).ValidAt a ↔
    ∃ P, ValidTransferNode (movingSlotSystem value childBound pivotBound)
      ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency P := by
  let d := movingNodeWord (childBound (n + 1)) (pivotBound (n + 1))
  let env : Bool → HistoryFormula Bool := fun b =>
    if b then .product R (.external (MovingSlotReversal.naturalProduct value CR))
    else .product L (.external (MovingSlotReversal.naturalProduct value CL))
  let x : Bool → ℕ := fun b => if b then XR * MovingSlotReversal.naturalProduct value CR
    else XL * MovingSlotReversal.naturalProduct value CL
  have henv (b : Bool) : (env b).value (fun j => (a j : ℚ)) = (x b : ℚ) := by
    cases b <;> simp only [env, x, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      HistoryFormula.value_product, HistoryFormula.value_external, hL, hR,
      Nat.cast_mul, Int.cast_natCast]
  have hh := wordTransferGuard_iff d (.leaf []) (.leaf []) s left.frequency right.frequency hs env a x henv
  change (wordTransferGuard d s left.frequency right.frequency hs env).ValidAt a ↔ _
  rw [hh]
  apply exists_congr
  intro P
  have hpL : wordTransferLeft ((WordTransferTemplate.node d (.leaf []) (.leaf [])).state x) =
      XL * MovingSlotReversal.naturalProduct value CL := by simp [wordTransferLeft, WordTransferTemplate.state, d, movingNodeWord, x]
  have hpR : wordTransferRight ((WordTransferTemplate.node d (.leaf []) (.leaf [])).state x) =
      XR * MovingSlotReversal.naturalProduct value CR := by simp [wordTransferRight, WordTransferTemplate.state, d, movingNodeWord, x]
  constructor <;> intro h
  · exact ⟨h.root_ne_zero, by simpa only [wordTransferSystem, hpR, movingSlotSystem, MovingSlotState.rightProduct] using h.root_unit,
      by simpa only [wordTransferSystem, hpL, hpR, movingSlotSystem, MovingSlotState.leftProduct, MovingSlotState.rightProduct] using h.relation,
      h.pivot_pos, h.pivot_bound, h.left_bound, h.right_bound,
      by simpa only [wordTransferSystem, hpR, movingSlotSystem, MovingSlotState.rightProduct, wordTransferPivotBound, wordTransferChildBound, WordTransferTemplate.state, d, movingNodeWord, wordTransferRight, x, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Bool.true_eq, ite_true, if_true, Nat.mul_one] using h.range_gap, h.pivot_unit⟩
  · exact ⟨h.root_ne_zero, by simpa only [wordTransferSystem, hpR, movingSlotSystem, MovingSlotState.rightProduct] using h.root_unit,
      by simpa only [wordTransferSystem, hpL, hpR, movingSlotSystem, MovingSlotState.leftProduct, MovingSlotState.rightProduct] using h.relation,
      h.pivot_pos, h.pivot_bound, h.left_bound, h.right_bound,
      by simpa only [wordTransferSystem, hpR, movingSlotSystem, MovingSlotState.rightProduct, wordTransferPivotBound, wordTransferChildBound, WordTransferTemplate.state, d, movingNodeWord, wordTransferRight, x, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Bool.true_eq, ite_true, if_true, Nat.mul_one] using h.range_gap, h.pivot_unit⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantFormulas
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational formulas retain the actual compensation division -/

namespace Ostmann
open scoped Classical

/-- A supported integer reconstruction evaluates the rational giant formula
exactly. The sampled compensation product appears in its denominator. -/
theorem MovingSlotReversal.giantFormula_value {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ)
    (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (XL XR : ℕ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ))
    (hI : step.IntegralAt value (XL, XR)) :
    (step.giantFormula value hs hu L R).value (fun b => (a b : ℚ)) =
      (step.naturalPivot value XL XR : ℚ) := by
  have he := congrArg (fun z : ℤ => (z : ℚ)) hI.2
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
  simp only [giantFormula, HistoryFormula.value_solve, HistoryFormula.value_product,
    HistoryFormula.value_external, hL, hR, Int.cast_mul, Int.cast_natCast]
  apply (div_eq_iff (mul_ne_zero (Int.cast_ne_zero.mpr hs) (Nat.cast_ne_zero.mpr hu))).mpr
  nlinarith only [he]

/-- The extra division by u is represented by an integer-polynomial residue
test. It is not discarded when the ordinary transfer guards are idealized. -/
theorem rational_nat_div_integral_iff (P u : ℕ) (hu : u ≠ 0) :
    (∃ z : ℤ, (P : ℚ) / u = (z : ℚ)) ↔ u ∣ P := by
  constructor
  · rintro ⟨z, hz⟩
    have he := (div_eq_iff (Nat.cast_ne_zero.mpr hu)).mp hz
    have hi : (P : ℤ) = z * (u : ℤ) := by exact_mod_cast he
    have hd : (u : ℤ) ∣ (P : ℤ) := ⟨z, by simpa only [mul_comm] using hi⟩
    exact Int.natCast_dvd_natCast.mp hd
  · rintro ⟨z, rfl⟩
    refine ⟨(z : ℤ), ?_⟩
    simp only [Nat.cast_mul, Int.cast_natCast]
    exact mul_div_cancel_left₀ (z : ℚ) (Nat.cast_ne_zero.mpr hu)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFormulaNodes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All rational node formulas of the concrete moving sampler -/

namespace Ostmann
open scoped Classical

/-- Every node formula is constructed before the top giants are evaluated.
Nonzero original coefficients imply all its exact arithmetic guard and
compensation-integrality tests, including both recursive branches. -/
theorem movingSlotWeight_formulaNodes {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : HistoryFormula Bool) (a : Bool → ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ))
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t ≠ 0) :
    ∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R,
      f.guard.ValidAt a ∧ f.newGiant.IntegralAt a := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR L R with
  | leaf s regular => simp [MovingSlotData.formulaNodes]
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    let step := MovingSlotData.step s CL CR u left right false
    let p := step.naturalPivot value XL XR
    let G := step.giantFormula value hf.1
      (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R
    have hI := movingSlotWeight_nonzero_integral value childBound pivotBound F extra
      (.node s CL CR u left right) t hT XL XR hw
    have hG : G.value (fun b => (a b : ℚ)) = (p : ℚ) :=
      step.giantFormula_value value hf.1 (MovingSlotReversal.naturalProduct_ne_zero value hvalue u)
        L R a XL XR hL hR hI.1
    have hGI : G.IntegralAt a := ⟨(p : ℤ), by simpa only [Int.cast_natCast] using hG⟩
    obtain ⟨Q, hQ, _, _⟩ := recursiveTransferWeight_nonzero_valid sys F cutoff (n + 1) x t hw
    have hQ' : ValidTransferNode sys x s left.frequency right.frequency Q := by
      simpa only [← hT.1, ← hT.2.1.root, ← hT.2.2.root] using hQ
    have hg := (movingNodeGuard_iff value childBound pivotBound s CL CR u left right hf.1
      XL XR L R a hL hR).mpr ⟨Q, hQ'⟩
    have hQp : Q / MovingSlotReversal.naturalProduct value u = p := by
      rw [← hQ.historyPivot_eq]
      simp only [historyPivot, sys, movingSlotSystem, MovingSlotState.leftProduct,
        MovingSlotState.rightProduct, x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root,
        p, step, MovingSlotReversal.naturalPivot, MovingSlotData.step, movingGiantPivot, Nat.mul_one]
    have hnode := recursiveTransferWeight_node sys F cutoff n x t Q hQ
    have hnL : recursiveTransferWeight sys F cutoff n ⟨n, left, p, XL⟩ t.2.1 ≠ 0 := by
      intro hz
      apply hw
      rw [hnode]
      change (cutoff x t.1 _ _ : ℂ) * recursiveTransferWeight sys F cutoff n
        ⟨n, left, Q / _, XL⟩ t.2.1 * _ = 0
      rw [hQp, hz, mul_zero, zero_mul]
    have hnR : recursiveTransferWeight sys F cutoff n ⟨n, right, p, XR⟩ t.2.2 ≠ 0 := by
      intro hz
      apply hw
      rw [hnode]
      change _ * star (recursiveTransferWeight sys F cutoff n ⟨n, right, Q / _, XR⟩ t.2.2) = 0
      rw [hQp, hz, star_zero, mul_zero]
    have hl := ihL t.2.1 hT.2.1 hf.2.1 p XL G L hG hL hnL
    have hr := ihR t.2.2 hT.2.2 hf.2.2 p XR G R hG hR hnR
    intro f hmem
    rcases List.mem_cons.mp hmem with h | h
    · subst f
      exact ⟨hg, hGI⟩
    · rcases List.mem_append.mp h with h | h
      · exact hl f h
      · exact hr f h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact arithmetic support of the constructed moving formulas -/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.giantFormula_of_composite {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ)
    (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (XL XR Q : ℕ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ))
    (hQ : step.leftFrequency * ((XR * MovingSlotReversal.naturalProduct value step.rightSlots : ℕ) : ℤ) -
      step.rightFrequency * ((XL * MovingSlotReversal.naturalProduct value step.leftSlots : ℕ) : ℤ) =
        step.rootFrequency * (Q : ℤ)) :
    (step.giantFormula value hs hu L R).value (fun b => (a b : ℚ)) =
      (Q : ℚ) / MovingSlotReversal.naturalProduct value step.compensationSlots := by
  have he := congrArg (fun z : ℤ => (z : ℚ)) hQ
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
  simp only [giantFormula, HistoryFormula.value_solve, HistoryFormula.value_product,
    HistoryFormula.value_external, hL, hR, Int.cast_mul, Int.cast_natCast]
  rw [he]
  field_simp

/-- The finite list of rational formulas characterizes every original
arithmetic condition. In particular the reverse implication retains the
compensation divisibility; no new support assumption is introduced. -/
theorem MovingSlotData.formulaNodes_iff {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ)
    (L R : HistoryFormula Bool) (a : Bool → ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ)) :
    (∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R,
      f.guard.ValidAt a ∧ f.newGiant.IntegralAt a) ↔
      T.ArithmeticSupport value childBound pivotBound XL XR := by
  induction T generalizing XL XR L R with
  | leaf s regular => simp [formulaNodes, ArithmeticSupport]
  | @node n s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    let U := MovingSlotReversal.naturalProduct value u
    have hU : U ≠ 0 := MovingSlotReversal.naturalProduct_ne_zero value hvalue u
    let G := step.giantFormula value hf.1 hU L R
    let g := movingNodeGuard (MovingSlotReversal.naturalProduct value CL)
      (MovingSlotReversal.naturalProduct value CR) s left.frequency right.frequency hf.1
      (childBound (n + 1)) (pivotBound (n + 1)) L R
    have hg := movingNodeGuard_iff value childBound pivotBound s CL CR u left right hf.1 XL XR L R a hL hR
    have hformula (Q : ℕ)
        (hQ : ValidTransferNode (movingSlotSystem value childBound pivotBound)
          ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency Q) :
        G.value (fun b => (a b : ℚ)) = (Q : ℚ) / U := by
      apply step.giantFormula_of_composite value hf.1 hU L R a XL XR Q hL hR
      exact hQ.relation
    have hGint (Q : ℕ)
        (hQ : ValidTransferNode (movingSlotSystem value childBound pivotBound)
          ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency Q) :
        G.IntegralAt a ↔ U ∣ Q := by
      simp only [HistoryFormula.IntegralAt, hformula Q hQ]
      exact rational_nat_div_integral_iff Q U hU
    have hGvalue (Q : ℕ)
        (hQ : ValidTransferNode (movingSlotSystem value childBound pivotBound)
          ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency Q)
        (hdiv : U ∣ Q) : G.value (fun b => (a b : ℚ)) = (Q / U : ℕ) := by
      rw [hformula Q hQ]
      calc
        (Q : ℚ) / U = ((U * (Q / U) : ℕ) : ℚ) / U :=
          congrArg (fun z : ℕ => (z : ℚ) / U) (Nat.mul_div_cancel' hdiv).symm
        _ = _ := by
          rw [Nat.cast_mul]
          exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hU)
    change (∀ f ∈ ({ guard := g, newGiant := G } ::
      (left.formulaNodes value hvalue childBound pivotBound hf.2.1 G L ++
        right.formulaNodes value hvalue childBound pivotBound hf.2.2 G R) : List MovingFormulaNode),
      f.guard.ValidAt a ∧ f.newGiant.IntegralAt a) ↔ _
    constructor
    · intro hall
      have hroot := hall ⟨g, G⟩ (by simp)
      obtain ⟨Q, hQ⟩ := hg.mp hroot.1
      have hd := (hGint Q hQ).mp hroot.2
      have hv := hGvalue Q hQ hd
      refine ⟨Q, hQ, hd, ?_, ?_⟩
      · apply (ihL hf.2.1 (Q / U) XL G L hv hL).mp
        intro f hmem
        exact hall f (List.mem_cons_of_mem _ (List.mem_append_left _ hmem))
      · apply (ihR hf.2.2 (Q / U) XR G R hv hR).mp
        intro f hmem
        exact hall f (List.mem_cons_of_mem _ (List.mem_append_right _ hmem))
    · rintro ⟨Q, hQ, hd, hl, hr⟩
      have hv := hGvalue Q hQ hd
      have hleft := (ihL hf.2.1 (Q / U) XL G L hv hL).mpr hl
      have hright := (ihR hf.2.2 (Q / U) XR G R hv hR).mpr hr
      intro f hmem
      rcases List.mem_cons.mp hmem with h | h
      · subst f
        exact ⟨hg.mpr ⟨Q, hQ⟩, (hGint Q hQ).mpr hd⟩
      · rcases List.mem_append.mp h with h | h
        · exact hleft f h
        · exact hright f h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingResidueTests
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three explicit residue tests at each original moving node -/

namespace Ostmann
open scoped Classical BigOperators

theorem formula_integral_small_test (F : HistoryFormula Bool) (a : Bool → ℤ) :
    F.IntegralAt a ↔ smallDivisionTest
      (MvPolynomial.eval₂Hom (RingHom.id ℤ) a F.cleared.numerator) F.cleared.denominator 1 := by
  rw [F.integralAt_iff]
  have hu (z : ℤ) : IsUnit (z : ZMod 1) := by
    rw [Subsingleton.elim (z : ZMod 1) 1]
    exact isUnit_one
  simp only [smallDivisionTest, hu, and_true]

theorem MovingFormulaNode.residueTests_iff (f : MovingFormulaNode) (a : Bool → ℤ) :
    f.residueTests a ↔ f.guard.residueAt a ∧ f.newGiant.IntegralAt a := by
  simp only [residueTests, testFormulas, testModuli, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Fin.forall_fin_zero, and_true, WordTransferGuard.residueAt, ← formula_integral_small_test,
    and_assoc]

theorem MovingFormulaNode.test_period_dvd (f : MovingFormulaNode) (j : Fin 3) :
    (f.testFormulas j).cleared.denominator * (f.testModuli j : ℤ) ∣ (f.residuePeriod : ℤ) := by
  apply Int.dvd_natCast.mpr
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  exact Finset.dvd_prod_of_mem (fun j : Fin 3 =>
    (f.testFormulas j).cleared.denominator.natAbs * f.testModuli j) (Finset.mem_univ j)

/-- All three tests are constant on the constructed residue classes. -/
theorem MovingFormulaNode.residueTests_modEq (f : MovingFormulaNode)
    (a b : Bool → ℤ) (h : ∀ i, a i ≡ b i [ZMOD f.residuePeriod]) :
    f.residueTests a ↔ f.residueTests b := by
  apply forall_congr'
  intro j
  exact cleared_history_test_residue_invariant (f.testFormulas j).cleared.numerator
    a b f.residuePeriod (f.testFormulas j).cleared.denominator (f.testModuli j)
    (f.testFormulas j).cleared.denominator_ne_zero (f.test_period_dvd j) h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSupportCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed residue and root cells for full moving arithmetic support -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingArithmeticPeriod_dvd (nodes : List MovingFormulaNode)
    (f : MovingFormulaNode) (hf : f ∈ nodes) : f.residuePeriod ∣ movingArithmeticPeriod nodes :=
  List.dvd_prod (List.mem_map.mpr ⟨f, hf, rfl⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSupportWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the exact arithmetic indicator from the recursive weight -/

namespace Ostmann
open scoped Classical

theorem movingSlotWeight_arithmeticSupport {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t ≠ 0) :
    T.ArithmeticSupport value childBound pivotBound XL XR := by
  let a := topGiantInput XL XR
  have hL : (HistoryFormula.prime false).value (fun b => (a b : ℚ)) = (XL : ℚ) := by
    simp [a, topGiantInput]
  have hR : (HistoryFormula.prime true).value (fun b => (a b : ℚ)) = (XR : ℚ) := by
    simp [a, topGiantInput]
  exact (T.formulaNodes_iff value hvalue childBound pivotBound hf XL XR _ _ a hL hR).mp
    (movingSlotWeight_formulaNodes value hvalue childBound pivotBound F extra T t hT hf
      XL XR _ _ a hL hR hw)

/-- The support indicator itself forces the exact positive integer recursion. -/
theorem MovingSlotData.ArithmeticSupport.integral {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hsupport : T.ArithmeticSupport value childBound pivotBound XL XR) :
    T.Integral value XL XR := by
  induction T generalizing XL XR with
  | leaf => trivial
  | @node n s CL CR u left right ihL ihR =>
    obtain ⟨Q, hQ, hdiv, hleft, hright⟩ := hsupport
    let U := MovingSlotReversal.naturalProduct value u
    let step := MovingSlotData.step s CL CR u left right false
    have hU : 0 < U := Nat.pos_of_ne_zero (MovingSlotReversal.naturalProduct_ne_zero value hvalue u)
    have hp : step.naturalPivot value XL XR = Q / U := by
      change reconstructedPivot _ s / U = Q / U
      congr 1
      apply reconstructedPivot_of_eq _ _ hQ.root_ne_zero Q
      simpa only [step, MovingSlotData.step, Nat.mul_one, movingSlotSystem,
        MovingSlotState.leftProduct, MovingSlotState.rightProduct] using hQ.relation
    have hQeq : Q = U * (Q / U) := (Nat.mul_div_cancel' hdiv).symm
    change (step.IntegralAt value (XL, XR) ∧ _ ∧ _)
    refine ⟨?_, ?_, ?_⟩
    · change 0 < step.naturalPivot value XL XR ∧ _
      rw [hp]
      refine ⟨Nat.div_pos (Nat.le_of_dvd hQ.pivot_pos hdiv) hU, ?_⟩
      change left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
        right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ) =
          s * ((U * (Q / U) : ℕ) : ℤ)
      rw [← hQeq]
      exact hQ.relation
    · rw [hp]
      exact ihL _ _ hleft
    · rw [hp]
      exact ihR _ _ hright

/-- On the derived support every guard evaluates to one, so only the original
leaf weights and extra node factors remain. -/
theorem movingSlotWeight_eq_unrestricted {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) (hsupport : T.ArithmeticSupport value childBound pivotBound XL XR) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
        movingUnrestrictedWeight value F extra T XL XR := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR with
  | leaf s regular =>
    have hs : s = t := hT
    simp only [recursiveTransferWeight, movingUnrestrictedWeight, hs]
  | @node n s CL CR u left right ihL ihR =>
    obtain ⟨Q, hQ, hdiv, hleft, hright⟩ := hsupport
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    let U := MovingSlotReversal.naturalProduct value u
    let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
    have hU : 0 < U := Nat.pos_of_ne_zero (MovingSlotReversal.naturalProduct_ne_zero value hvalue u)
    have hQ' : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) Q := by
      simpa only [← hT.1, ← hT.2.1.root, ← hT.2.2.root] using hQ
    have hp : Q / U = p := by
      rw [← hQ'.historyPivot_eq]
      simp only [historyPivot, sys, movingSlotSystem, MovingSlotState.leftProduct,
        MovingSlotState.rightProduct, x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root,
        p, MovingSlotReversal.naturalPivot, MovingSlotData.step, movingGiantPivot, Nat.mul_one, U]
    have hc : cutoff x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
        extra x s left.frequency right.frequency := by
      change (if 0 < U ∧ U ∣ historyPivot sys x t.1 _ _ then _ else 0) = _
      rw [hQ'.historyPivot_eq, ite_eq_left ⟨hU, hdiv⟩]
      simp only [← hT.1, ← hT.2.1.root, ← hT.2.2.root]
    rw [recursiveTransferWeight_node sys F cutoff n x t Q hQ', hc]
    change (extra x s left.frequency right.frequency : ℂ) *
      recursiveTransferWeight sys F cutoff n ⟨n, left, Q / U, XL⟩ t.2.1 *
      star (recursiveTransferWeight sys F cutoff n ⟨n, right, Q / U, XR⟩ t.2.2) = _
    rw [ihL t.2.1 hT.2.1 (Q / U) XL hleft, ihR t.2.2 hT.2.2 (Q / U) XR hright, hp]
    rfl

/-- This factorization includes every zero-support term; it is suitable for
weighted prime sums without conditioning away the original arithmetic tests. -/
theorem movingSlotWeight_indicator_factor {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
        movingArithmeticIndicator value childBound pivotBound T XL XR *
          movingUnrestrictedWeight value F extra T XL XR := by
  by_cases hs : T.ArithmeticSupport value childBound pivotBound XL XR
  · rw [movingArithmeticIndicator, ite_eq_left hs, one_mul]
    exact movingSlotWeight_eq_unrestricted value hvalue childBound pivotBound F extra T t hT XL XR hs
  · rw [movingArithmeticIndicator, ite_eq_right hs, zero_mul]
    by_contra hn
    exact hs (movingSlotWeight_arithmeticSupport value hvalue childBound pivotBound F extra T t hT hf XL XR hn)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed residue representatives for the literal spectator recursion -/

namespace Ostmann
open scoped Classical

/-- Clearing the input period makes division compatible with congruence,
even when the individual numerators are not divisible by the denominator. -/
theorem int_modEq_ediv (c m x y : ℤ) (hc : c ≠ 0)
    (h : x ≡ y [ZMOD c * m]) : x / c ≡ y / c [ZMOD m] := by
  have hr : x % c = y % c := h.of_mul_right m
  have hrem : x % c ≡ y % c [ZMOD c * m] := by rw [hr]
  have hx : x - x % c = c * (x / c) := by
    linear_combination -(Int.emod_add_mul_ediv x c)
  have hy : y - y % c = c * (y / c) := by
    linear_combination -(Int.emod_add_mul_ediv y c)
  have hh := h.sub hrem
  rw [hx, hy] at hh
  exact Int.ModEq.mul_left_cancel' hc hh

theorem MovingSlotReversal.signedPivot_nat {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (hs : s.rootFrequency ≠ 0)
    (XL XR : ℕ) (hI : s.IntegralAt value (XL, XR)) :
    s.signedPivot value XL XR = (s.naturalPivot value XL XR : ℤ) := by
  have he := hI.2
  simp only [Nat.cast_mul] at he
  unfold signedPivot
  rw [he, ← mul_assoc]
  exact Int.mul_ediv_cancel_left _
    (mul_ne_zero hs (Nat.cast_ne_zero.mpr (naturalProduct_ne_zero value hvalue _)))

/-- Signed representatives agree with the original natural recursion on
its proved integral support. No extra unit condition is imposed. -/
theorem movingSignedSpectator_nat {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ)
    (hI : T.Integral value XL XR) :
    movingSignedSpectator value g D T XL XR = movingSlotSpectator value g D T XL XR := by
  induction T generalizing XL XR with
  | leaf s regular =>
    simp only [movingSignedSpectator, movingSlotSpectator, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  | node s CL CR U left right ihL ihR =>
    rw [movingSignedSpectator, movingSlotSpectator,
      (MovingSlotData.step s CL CR U left right false).signedPivot_nat value hvalue hf.1 XL XR hI.1]
    simp only [Int.cast_natCast]
    split_ifs
    · rfl
    · rw [ihL hf.2.1 _ _ hI.2.1, ihR hf.2.2 _ _ hI.2.2]

theorem MovingSlotReversal.signedPivot_modEq {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (hs : s.rootFrequency ≠ 0)
    (XL XR YL YR m : ℤ)
    (hL : XL ≡ YL [ZMOD s.rootFrequency * (naturalProduct value s.compensationSlots : ℤ) * m])
    (hR : XR ≡ YR [ZMOD s.rootFrequency * (naturalProduct value s.compensationSlots : ℤ) * m]) :
    s.signedPivot value XL XR ≡ s.signedPivot value YL YR [ZMOD m] := by
  unfold signedPivot
  apply int_modEq_ediv _ m _ _
    (mul_ne_zero hs (Nat.cast_ne_zero.mpr (naturalProduct_ne_zero value hvalue _)))
  exact ((hR.mul_right (naturalProduct value s.rightSlots)).mul_left s.leftFrequency).sub
    ((hL.mul_right (naturalProduct value s.leftSlots)).mul_left s.rightFrequency)

/-- Signed representatives are periodic before imposing any real support. -/
theorem movingSignedSpectator_modEq {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR YL YR : ℤ)
    (hL : (XL : ℤ) ≡ (YL : ℤ) [ZMOD (q : ℤ) * movingSpectatorDenominator value T])
    (hR : (XR : ℤ) ≡ (YR : ℤ) [ZMOD (q : ℤ) * movingSpectatorDenominator value T]) :
    movingSignedSpectator value g D T XL XR = movingSignedSpectator value g D T YL YR := by
  induction T generalizing XL XR YL YR with
  | leaf s regular =>
    simp only [movingSpectatorDenominator, mul_one] at hL hR
    have hl : (XL : ZMod q) = (YL : ZMod q) := by
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ q).mpr hL
    have hr : (XR : ZMod q) = (YR : ZMod q) := by
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ q).mpr hR
    simp only [movingSignedSpectator, Int.cast_mul, Int.cast_natCast, hl, hr]
  | node s CL CR U left right ihL ihR =>
    let c : ℤ := s * (MovingSlotReversal.naturalProduct value U : ℤ)
    let dl := movingSpectatorDenominator value left
    let dr := movingSpectatorDenominator value right
    let step := MovingSlotData.step s CL CR U left right false
    let p := step.signedPivot value XL XR
    let r := step.signedPivot value YL YR
    have hL' : (XL : ℤ) ≡ (YL : ℤ) [ZMOD c * ((q : ℤ) * dl * dr)] := by
      convert hL using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [c, dl, dr, movingSpectatorDenominator]
      ring
    have hR' : (XR : ℤ) ≡ (YR : ℤ) [ZMOD c * ((q : ℤ) * dl * dr)] := by
      convert hR using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [c, dl, dr, movingSpectatorDenominator]
      ring
    have hp : (p : ℤ) ≡ (r : ℤ) [ZMOD (q : ℤ) * dl * dr] :=
      step.signedPivot_modEq value hvalue hf.1 XL XR YL YR _ hL' hR'
    have hpq : (p : ZMod q) = (r : ZMod q) := by
      have hp' := hp.of_dvd (show (q : ℤ) ∣ (q : ℤ) * dl * dr from
        ⟨dl * dr, by ring⟩)
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ q).mpr hp'
    have hpl : (p : ℤ) ≡ (r : ℤ) [ZMOD (q : ℤ) * dl] :=
      hp.of_dvd ⟨dr, rfl⟩
    have hpr : (p : ℤ) ≡ (r : ℤ) [ZMOD (q : ℤ) * dr] :=
      hp.of_dvd ⟨dl, by ring⟩
    have hll : (XL : ℤ) ≡ (YL : ℤ) [ZMOD (q : ℤ) * dl] :=
      hL'.of_dvd ⟨c * dr, by ring⟩
    have hrr : (XR : ℤ) ≡ (YR : ℤ) [ZMOD (q : ℤ) * dr] :=
      hR'.of_dvd ⟨c * dl, by ring⟩
    have hl := ihL hf.2.1 p XL r YL hpl hll
    have hr := ihR hf.2.2 p XR r YR hpr hrr
    change (if (p : ZMod q) = 0 then 0 else
      movingSignedSpectator value g D left p XL * star (movingSignedSpectator value g D right p XR)) =
      (if (r : ZMod q) = 0 then 0 else
      movingSignedSpectator value g D left r YL * star (movingSignedSpectator value g D right r YR))
    rw [hpq, hl, hr]

theorem movingSlotSpectator_eq_residue {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hI : T.Integral value XL XR)
    (hM : (q : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    movingSlotSpectator value g D T XL XR = movingSignedSpectator value g D T a b := by
  rw [← movingSignedSpectator_nat value hvalue g D T hf XL XR hI]
  exact movingSignedSpectator_modEq value hvalue g D T hf XL XR a b
    (hL.of_dvd hM) (hR.of_dvd hM)

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

theorem int_modEq_isCoprime_iff {x y m : ℤ} (h : x ≡ y [ZMOD m]) :
    IsCoprime x m ↔ IsCoprime y m := by
  have transport {a b : ℤ} (hab : a ≡ b [ZMOD m]) (ha : IsCoprime a m) :
      IsCoprime b m := by
    obtain ⟨k, hk⟩ := hab.dvd
    obtain ⟨u, v, huv⟩ := ha
    refine ⟨u, v - u * k, ?_⟩
    linear_combination huv + u * hk
  exact ⟨transport h, transport h.symm⟩

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full pairwise and subtree-frequency support, with the top giant pair separated -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.currentPairwise_iff {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ) :
    T.CurrentPairwise value XL XR ↔ XL.Coprime XR ∧
      (T.regularSlots.map value).Pairwise Nat.Coprime ∧
      XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
      XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) := by
  simp only [CurrentPairwise, currentSlots, List.pairwise_cons, List.mem_cons,
    forall_eq_or_imp, MovingSlotReversal.naturalProduct, Nat.coprime_list_prod_right_iff]
  tauto

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full moving support as one explicit residue mask -/

namespace Ostmann
open scoped Classical

theorem movingSquareLineSupport_modEq {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR YL YR M : ℤ)
    (hM : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    movingSquareLineSupport value T XL XR ↔ movingSquareLineSupport value T YL YR := by
  apply forall₂_congr
  intro o ho
  apply forall₂_congr
  intro i hi
  have hl : (XL : ZMod (value i ^ 2)) = (YL : ZMod (value i ^ 2)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hL.of_dvd (by exact_mod_cast hM o ho i hi))
  have hr : (XR : ZMod (value i ^ 2)) = (YR : ZMod (value i ^ 2)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hR.of_dvd (by exact_mod_cast hM o ho i hi))
  dsimp only
  rw [hl, hr]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original arithmetic gate into residues and real inequalities -/

namespace Ostmann
open scoped Classical

/-- Integrality turns the strict integer gap into the closed real inequality.
All divisibility and unit tests remain in the residue factor. -/
theorem WordTransferGuard.validAt_residue_archimedean {σ : Type*}
    (g : WordTransferGuard σ) (x : σ → ℤ) :
    g.ValidAt x ↔ g.residueAt x ∧ g.frequencyBounds ∧
      g.archimedeanAt (fun i => (x i : ℝ)) := by
  change g.ValidAt x ↔ g.residueAt x ∧ g.frequencyBounds ∧
    (1 ≤ g.pivot.realValue x ∧ g.pivot.realValue x ≤ g.pivotBound ∧
      ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ) ≤ g.rightProduct.realValue x)
  constructor
  · rintro ⟨hp, hr, hlo, hhi, hgap, hv, hw⟩
    exact ⟨⟨hp, hr⟩, ⟨hv, hw⟩, hlo, hhi, (g.gap_iff x ⟨hp, hr⟩).mp hgap⟩
  · rintro ⟨⟨hp, hr⟩, ⟨hv, hw⟩, hlo, hhi, hgap⟩
    exact ⟨hp, hr, hlo, hhi, (g.gap_iff x ⟨hp, hr⟩).mpr hgap, hv, hw⟩

theorem MovingFormulaNode.holds_residue_archimedean (f : MovingFormulaNode) (a : Bool → ℤ) :
    (f.guard.ValidAt a ∧ f.newGiant.IntegralAt a) ↔
      f.residueTests a ∧ f.guard.frequencyBounds ∧
        f.guard.archimedeanAt (fun i => (a i : ℝ)) := by
  rw [f.guard.validAt_residue_archimedean, f.residueTests_iff]
  tauto

/-- The real factor is evaluated at the actual point, while the residue
factor may use any representative of the constructed common period. -/
theorem movingFormulaNodes_residue_real (nodes : List MovingFormulaNode)
    (x a : Bool → ℤ) (hres : ∀ i, x i ≡ a i [ZMOD movingArithmeticPeriod nodes]) :
    (∀ f ∈ nodes, f.guard.ValidAt x ∧ f.newGiant.IntegralAt x) ↔
      movingResidueGate nodes a ∧ movingArchimedeanGate nodes (fun i => (x i : ℝ)) := by
  have hfres (f : MovingFormulaNode) (hf : f ∈ nodes) : f.residueTests x ↔ f.residueTests a :=
    f.residueTests_modEq x a (fun i => (hres i).of_dvd
      (by exact_mod_cast movingArithmeticPeriod_dvd nodes f hf))
  constructor
  · intro h
    constructor
    · intro f hf
      have hx := (f.holds_residue_archimedean x).mp (h f hf)
      exact ⟨(hfres f hf).mp hx.1, hx.2.1⟩
    · intro f hf
      exact ((f.holds_residue_archimedean x).mp (h f hf)).2.2
  · rintro ⟨hr, ha⟩ f hf
    exact (f.holds_residue_archimedean x).mpr
      ⟨(hfres f hf).mpr (hr f hf).1, (hr f hf).2, ha f hf⟩

theorem movingArithmeticSupport_residue_real {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    T.ArithmeticSupport value childBound pivotBound XL XR ↔
      movingResidueGate nodes (topGiantInput a b) ∧ movingArchimedeanGate nodes (topGiantReal XL XR) := by
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  have hform := T.formulaNodes_iff value hvalue childBound pivotBound hf XL XR
    (.prime false) (.prime true) (topGiantInput XL XR) (by simp [topGiantInput]) (by simp [topGiantInput])
  rw [← hform]
  have hres : ∀ i, topGiantInput XL XR i ≡ topGiantInput a b i [ZMOD movingArithmeticPeriod nodes] := by
    intro i
    cases i
    · exact hL.of_dvd (by exact_mod_cast hM)
    · exact hR.of_dvd (by exact_mod_cast hM)
  have h := movingFormulaNodes_residue_real nodes (topGiantInput XL XR) (topGiantInput a b) hres
  have he : (fun i => (topGiantInput XL XR i : ℝ)) = topGiantReal XL XR := by
    funext i
    cases i <;> rfl
  simpa only [he] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingResidueFactorization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed residue factors separated from the real moving support -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingArithmeticIndicator_residue_real {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingArithmeticIndicator value childBound pivotBound T XL XR =
      movingResidueFlag nodes (topGiantInput a b) * movingArchimedeanFlag nodes (topGiantReal XL XR) := by
  dsimp only
  have h := movingArithmeticSupport_residue_real value hvalue childBound pivotBound T hf XL XR a b M hM hL hR
  unfold movingArithmeticIndicator movingResidueFlag movingArchimedeanFlag
  by_cases hr : movingResidueGate
      (T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)) (topGiantInput a b) <;>
    by_cases ha : movingArchimedeanGate
      (T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)) (topGiantReal XL XR) <;>
    simp only [h, hr, ha, and_self, and_false, false_and, ite_true, if_true, ite_false, if_false, mul_one, mul_zero]

/-- On a fixed top residue pair the original spectator coefficient is a
fixed signed-residue value. The only remaining variable gate is real. -/
theorem moving_arithmetic_spectator_residue_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) (g : ∀ i, ZMod (q i) → ℂ)
    (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingArithmeticIndicator value childBound pivotBound T XL XR *
        (∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR) =
      (movingResidueFlag nodes (topGiantInput a b) * movingArchimedeanFlag nodes (topGiantReal XL XR)) *
        movingSpectatorResidue q value g D S T a b := by
  dsimp only
  have hflag := movingArithmeticIndicator_residue_real value hvalue childBound pivotBound T hf XL XR a b M hM hL hR
  by_cases hs : T.ArithmeticSupport value childBound pivotBound XL XR
  · have hI := hs.integral value hvalue childBound pivotBound T XL XR
    have hspec : (∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR) =
        movingSpectatorResidue q value g D S T a b := by
      apply Finset.prod_congr rfl
      intro i hi
      exact movingSlotSpectator_eq_residue value hvalue (g i) (D i) T hf XL XR a b M hI (hMq i hi) hL hR
    rw [hspec, hflag]
  · have hz : movingArithmeticIndicator value childBound pivotBound T XL XR = 0 :=
      ite_eq_right hs
    rw [hz, zero_mul, ← hflag, hz, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingScalarWindows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The remaining original scalar and its literal terminal windows -/

namespace Ostmann
open scoped Classical

/-- Sharp terminal windows leave one fixed scalar coefficient. The test is
on the actual terminal moduli obtained by the integer moving recursion. -/
theorem movingUnrestrictedWeight_data_window {σ : Type*} (value : σ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    movingUnrestrictedWeight value (movingWindowLeaf value X lo hi (movingDataLeaf F))
        (movingDataExtra E) T XL XR =
      if ∀ i, (T.leafModuli value XL XR i : ℝ) / X ∈ Set.Icc lo hi
      then movingDataWeight F E T else 0 := by
  induction T generalizing XL XR with
  | leaf s regular =>
    simp only [movingUnrestrictedWeight, movingWindowLeaf, movingSlotModulus,
      movingDataLeaf, movingDataWeight, MovingSlotData.leafModuli, forall_const]
    rfl
  | @node n s CL CR U left right ihL ihR =>
    let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
    have hforall : (∀ i, ((MovingSlotData.node s CL CR U left right).leafModuli value XL XR i : ℝ) / X ∈ Set.Icc lo hi) ↔
        (∀ i, (left.leafModuli value p XL i : ℝ) / X ∈ Set.Icc lo hi) ∧
        (∀ i, (right.leafModuli value p XR i : ℝ) / X ∈ Set.Icc lo hi) := by
      constructor
      · intro h
        exact ⟨fun i => h (.inl i), fun i => h (.inr i)⟩
      · rintro ⟨hL, hR⟩ i
        cases i with
        | inl i => exact hL i
        | inr i => exact hR i
    rw [movingUnrestrictedWeight, ihL, ihR]
    simp only [movingDataExtra, movingDataWeight, hforall]
    by_cases hL : ∀ i, (left.leafModuli value p XL i : ℝ) / X ∈ Set.Icc lo hi <;>
      by_cases hR : ∀ i, (right.leafModuli value p XR i : ℝ) / X ∈ Set.Icc lo hi <;>
      simp only [p, hL, hR, forall_const, and_self, and_false, false_and, ite_true, if_true, ite_false, if_false,
        star_zero, zero_mul, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-depth cost of the constructed Fourier variation bound -/

namespace Ostmann
open scoped SchwartzMap

/-- Uniform in moving endpoints whose width has the actual exponential scale. -/
theorem movingFourierVariationBudget_exp_window (ψ : 𝓢(ℝ, ℂ)) (n : ℕ)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 ≤ m → ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) →
      movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n ≤
        Real.exp (C * (m + 1)) := by
  let B := SchwartzMap.seminorm ℝ 0 0 ψ
  let D := SchwartzMap.seminorm ℝ 0 1 ψ
  let K := 3 * B + D
  let r : ℝ := (2 ^ n : ℕ)
  have hB : 0 ≤ B := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD : 0 ≤ D := schwartz_profile_lip_nonneg ψ
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  refine ⟨r * (K + A + H + 1), by positivity, ?_⟩
  intro m hm lo hi hhi hwidth
  have heA : 1 ≤ Real.exp (A * m) := Real.one_le_exp_iff.mpr (mul_nonneg hA hm)
  have heH : 1 ≤ Real.exp (H * m) := Real.one_le_exp_iff.mpr (mul_nonneg hH hm)
  have heAll : Real.exp (A * m) * Real.exp (H * m) = Real.exp ((A + H) * m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hproduct : 1 ≤ Real.exp (A * m) * Real.exp (H * m) :=
    heH.trans (le_mul_of_one_le_left (Real.exp_nonneg _) heA)
  have hHproduct : Real.exp (H * m) ≤ Real.exp (A * m) * Real.exp (H * m) :=
    le_mul_of_one_le_left (Real.exp_nonneg _) heA
  have hpoly : 2 * B + (B + D * Real.exp (A * m)) * (hi - lo) ≤
      K * Real.exp ((A + H) * m) := by
    calc
      _ ≤ 2 * B + (B + D * Real.exp (A * m)) * Real.exp (H * m) := by gcongr
      _ ≤ K * (Real.exp (A * m) * Real.exp (H * m)) := by
        dsimp only [K]
        nlinarith [mul_le_mul_of_nonneg_left hproduct hB,
          mul_le_mul_of_nonneg_left hHproduct hB]
      _ = _ := by rw [heAll]
  have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have hbase : 2 * B + (B + D * Real.exp (A * m)) * (hi - lo) ≤
      Real.exp (K + (A + H) * m) := by
    rw [Real.exp_add]
    exact hpoly.trans (mul_le_mul_of_nonneg_right hKe (Real.exp_nonneg _))
  unfold movingFourierVariationBudget
  change (2 * B + (B + D * Real.exp (A * m)) * (hi - lo)) ^ (2 ^ n) ≤ _
  apply (pow_le_pow_left₀ (by positivity) hbase (2 ^ n)).trans
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  change r * (K + (A + H) * m) ≤ r * (K + A + H + 1) * (m + 1)
  nlinarith [mul_nonneg hK hm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCutoffPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All actual logarithmic node cutoffs as polynomial factors -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotData.nodeCutoffPolynomials_value {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (z : ℝ) :
    ((T.nodeCutoffPolynomials value L R).map
      (fun f => (positiveLogCutoff φ (G f.1) (f.2.eval z) : ℂ))).prod =
      movingRealNodeCutoff value φ G T (L.eval z) (R.eval z) := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [nodeCutoffPolynomials, List.map_cons, List.map_append, List.prod_cons,
      List.prod_append, ihL, ihR, MovingSlotReversal.pivotPolynomial_eval, movingRealNodeCutoff]
    ring

theorem movingNodeCutoffFactors_value {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    smoothPolynomialWeight (movingNodeCutoffFactors value T L R φ G B D hB hD hφ hlip) z =
      movingRealNodeCutoff value φ G T (L.eval z) (R.eval z) := by
  unfold smoothPolynomialWeight
  simp only [movingNodeCutoffFactors, logCutoffPolynomialFactor_value _ _ _ _ _ _ _ hφ hlip hout]
  rw [← T.nodeCutoffPolynomials_value value φ G L R z]
  exact (Fin.prod_ofFn _).symm.trans (congrArg List.prod
    (List.ofFn_getElem_eq_map (T.nodeCutoffPolynomials value L R)
      (fun f => (positiveLogCutoff φ (G f.1) (f.2.eval z) : ℂ))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingNodeCutoffFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping the original logarithmic cutoff in every moving node -/

namespace Ostmann
open scoped Classical

theorem movingNaturalNodeCutoff_star {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) {n : ℕ} (T : MovingSlotData σ n) (L R : ℕ) :
    star (movingNaturalNodeCutoff value φ G T L R) = movingNaturalNodeCutoff value φ G T L R := by
  have hstar (a : ℝ) : star (a : ℂ) = (a : ℂ) := by simp
  induction T generalizing L R with
  | leaf => simp only [movingNaturalNodeCutoff, star_one]
  | node s CL CR u left right ihL ihR =>
    simp only [movingNaturalNodeCutoff, star_mul, hstar, ihL, ihR]
    ring

/-- The smooth cutoff is factored out of the original recursion, even when
an arithmetic guard vanishes. All other node factors remain in `extra`. -/
theorem movingSlotWeight_node_cutoff {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t) (L R : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingPhiExtra value childBound pivotBound extra φ G))
        n ⟨n, T, L, R⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, L, R⟩ t *
          movingNaturalNodeCutoff value φ G T L R := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound extra
  let cutφ := movingSlotCutoff value childBound pivotBound (movingPhiExtra value childBound pivotBound extra φ G)
  induction T generalizing L R with
  | leaf s regular => simp only [recursiveTransferWeight, movingNaturalNodeCutoff, mul_one]
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, L, R⟩
    let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value L R
    have hp : historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
        MovingSlotReversal.naturalProduct value u = p := by
      simp only [historyPivot, sys, movingSlotSystem, MovingSlotState.leftProduct,
        MovingSlotState.rightProduct, x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root,
        p, MovingSlotReversal.naturalPivot, MovingSlotData.step, movingGiantPivot, Nat.mul_one]
    have hc : (cutφ x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) =
        (cut x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
          (positiveLogCutoff φ (G (n + 1)) p : ℂ) := by
      dsimp only [cutφ, cut, movingSlotCutoff, movingPhiExtra]
      split_ifs <;> simp only [Complex.ofReal_mul, Complex.ofReal_zero, zero_mul]
      congr 2
      change positiveLogCutoff φ (G (n + 1)) ((historyPivot sys x t.1 _ _ / MovingSlotReversal.naturalProduct value u : ℕ) : ℝ) = _
      rw [hp]
    change recursiveTransferWeight sys F cutφ (n + 1) x t = _
    simp only [recursiveTransferWeight]
    split_ifs
    · change (cutφ x t.1 _ _ : ℂ) *
          recursiveTransferWeight sys F cutφ n ⟨n, left, _, L⟩ t.2.1 *
          star (recursiveTransferWeight sys F cutφ n ⟨n, right, _, R⟩ t.2.2) =
        ((cut x t.1 _ _ : ℂ) * recursiveTransferWeight sys F cut n ⟨n, left, _, L⟩ t.2.1 *
          star (recursiveTransferWeight sys F cut n ⟨n, right, _, R⟩ t.2.2)) * _
      rw [hp, hc, ihL t.2.1 hT.2.1 p L, ihR t.2.2 hT.2.2 p R]
      simp only [star_mul, movingNaturalNodeCutoff_star]
      change _ = _ * ((positiveLogCutoff φ (G (n + 1)) p : ℂ) *
        movingNaturalNodeCutoff value φ G left p L * movingNaturalNodeCutoff value φ G right p R)
      ring
    · exact (zero_mul _).symm

theorem movingNaturalNodeCutoff_eq_real {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (L R : ℕ) (hI : T.Integral value L R) :
    movingNaturalNodeCutoff value φ G T L R = movingRealNodeCutoff value φ G T L R := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).realPivot_eq value L R hf.1
      (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) hI.1
    simp only [movingNaturalNodeCutoff, movingRealNodeCutoff, hp,
      ihL hf.2.1 _ _ hI.2.1, ihR hf.2.2 _ _ hI.2.2]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSmoothPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One polynomial family for all node cutoffs and Fourier leaves -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingSmoothPolynomialFactors_value {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    smoothPolynomialWeight (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip) z =
      smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z *
        movingRealNodeCutoff value φ G T (L.eval z) (R.eval z) := by
  simp only [smoothPolynomialWeight, movingSmoothPolynomialFactors, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right]
  exact congrArg (_ * ·) (movingNodeCutoffFactors_value value T L R φ G B D hB hD hφ hlip hout z)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullSmooth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original smooth factor in the moving arithmetic coefficient -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- Every original logarithmic node cutoff and normalized Fourier leaf is
represented by the one constructed polynomial family. Arithmetic restrictions
and compensation powers stay in the original scalar coefficient. -/
theorem moving_full_smooth_polynomial {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : Polynomial ℝ) (z : ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => movingWindowLeaf value X lo hi F x s * movingFourierLeaf value ψ X x s)
        (movingSlotCutoff value childBound pivotBound
          (movingPhiExtra value childBound pivotBound extra φ G)) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
        n ⟨n, T, XL, XR⟩ t *
          smoothPolynomialWeight (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
            φ G B D hB hD hφ hlip) z := by
  rw [movingSlotWeight_node_cutoff value childBound pivotBound _ extra φ G T t hT XL XR,
    moving_windowed_fourier_polynomial value hvalue childBound pivotBound F extra ψ X lo hi
      hlo hhi T t hT hfreq XL XR L R z hL hR]
  by_cases hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
      n ⟨n, T, XL, XR⟩ t = 0
  · simp only [hw, zero_mul]
  · have hI := movingSlotWeight_nonzero_integral value childBound pivotBound
      (movingWindowLeaf value X lo hi F) extra T t hT XL XR hw
    rw [movingNaturalNodeCutoff_eq_real value hvalue φ G T hfreq XL XR hI,
      movingSmoothPolynomialFactors_value value T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout z,
      hL, hR]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_MovingSpectatorZero
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The spectator zero convention eliminates inserted nonunits -/

namespace Ostmann
open scoped Classical

/-- A giant which is zero at an outside prime survives along one child path
until a leaf. Its zero contribution is thus forced by the original transform. -/
theorem movingSlotSpectator_zero {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (hg : g 0 = 0) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hzero : (XL : ZMod q) = 0 ∨ (XR : ZMod q) = 0) :
    movingSlotSpectator value g D T XL XR = 0 := by
  induction T generalizing XL XR with
  | leaf s regular =>
    rcases hzero with h | h <;>
      simp only [movingSlotSpectator, Nat.cast_mul, h, zero_mul, mul_zero, div_zero, hg]
  | node s CL CR U left right ihL ihR =>
    simp only [movingSlotSpectator]
    split_ifs
    · rfl
    · rcases hzero with h | h
      · rw [ihL _ _ (Or.inr h), zero_mul]
      · rw [ihR _ _ (Or.inr h), star_zero, mul_zero]

/-- For the actual transforms (which vanish at zero), no extra hypothesis
that the composite pivot is a unit is needed for spectator factorization. -/
theorem movingSlotWeight_spectator_of_zero {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (g : ZMod q → ℂ) (hg : g 0 = 0) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => F x s * spectatorHistoryLeaf (movingSlotModulus value) g D x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t *
      movingSlotSpectator value g D T XL XR := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR with
  | leaf s regular =>
    have hs : s = t := hT
    simp only [recursiveTransferWeight, spectatorHistoryLeaf, movingSlotModulus,
      movingSlotSpectator, hs]
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    by_cases hw : recursiveTransferWeight sys F cutoff (n + 1) x t = 0
    · rw [recursiveTransferWeight_mul_leaf]
      change recursiveTransferWeight sys F cutoff (n + 1) x t * _ =
        recursiveTransferWeight sys F cutoff (n + 1) x t * _
      rw [hw, zero_mul, zero_mul]
    · obtain ⟨P, hvalid, _, _⟩ := recursiveTransferWeight_nonzero_valid sys F cutoff _ x t hw
      have hnode := recursiveTransferWeight_node sys F cutoff n x t P hvalid
      have hcut : cutoff x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ≠ 0 := by
        intro hz
        apply hw
        rw [hnode, hz, Complex.ofReal_zero, zero_mul, zero_mul]
      have hdiv : 0 < MovingSlotReversal.naturalProduct value u ∧
          MovingSlotReversal.naturalProduct value u ∣ P := by
        by_contra hd
        apply hcut
        change (if 0 < MovingSlotReversal.naturalProduct value u ∧
          MovingSlotReversal.naturalProduct value u ∣ historyPivot sys x t.1 _ _ then _ else 0) = 0
        rw [hvalid.historyPivot_eq]
        exact ite_eq_right hd
      let p := P / MovingSlotReversal.naturalProduct value u
      have hP : P = MovingSlotReversal.naturalProduct value u * p :=
        (Nat.mul_div_cancel' hdiv.2).symm
      have hrel : left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
          right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ) =
          s * ((MovingSlotReversal.naturalProduct value u * p : ℕ) : ℤ) := by
        simpa only [sys, movingSlotSystem, MovingSlotState.leftProduct, MovingSlotState.rightProduct,
          x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root, hP, Int.cast_natCast] using hvalid.relation
      have hnat : (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR = p := by
        unfold MovingSlotReversal.naturalPivot movingGiantPivot
        simp only [MovingSlotData.step, Nat.mul_one]
        rw [reconstructedPivot_of_eq _ _ (by simpa only [← hT.1] using hvalid.root_ne_zero)
          (MovingSlotReversal.naturalProduct value u * p) hrel]
        exact Nat.mul_div_cancel_left p hdiv.1
      rw [recursiveTransferWeight_node _ _ _ _ _ _ P hvalid, hnode]
      change (cutoff x t.1 _ _ : ℂ) *
          recursiveTransferWeight sys (fun x s => F x s * spectatorHistoryLeaf (movingSlotModulus value) g D x s)
            cutoff n ⟨n, left, p, XL⟩ t.2.1 *
          star (recursiveTransferWeight sys (fun x s => F x s * spectatorHistoryLeaf (movingSlotModulus value) g D x s)
            cutoff n ⟨n, right, p, XR⟩ t.2.2) =
        ((cutoff x t.1 _ _ : ℂ) * recursiveTransferWeight sys F cutoff n ⟨n, left, p, XL⟩ t.2.1 *
          star (recursiveTransferWeight sys F cutoff n ⟨n, right, p, XR⟩ t.2.2)) * _
      rw [ihL t.2.1 hT.2.1 p XL, ihR t.2.2 hT.2.2 p XR]
      rw [movingSlotSpectator, hnat]
      by_cases hp : (p : ZMod q) = 0
      · rw [ite_eq_left hp, mul_zero, movingSlotSpectator_zero value g hg D left p XL (Or.inl hp), mul_zero, mul_zero]
        simp only [zero_mul]
      · rw [ite_eq_right hp, star_mul]
        ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_MovingFullSmoothZero
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full smooth coefficients with only the actual spectator zero convention -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap

/-- Factor every spectator while retaining the full smooth and arithmetic
coefficient. This identity includes zero-support terms. -/
theorem movingSlotWeight_spectator_product_of_zero {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => F x s * ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (D i) x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t *
        ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp only [Finset.prod_empty, mul_one]
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    have he : (fun x s => F x s * (spectatorHistoryLeaf (movingSlotModulus value) (g i) (D i) x s *
        ∏ j ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g j) (D j) x s)) =
        (fun x s => (F x s * ∏ j ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g j) (D j) x s) *
          spectatorHistoryLeaf (movingSlotModulus value) (g i) (D i) x s) := by
      funext x s
      ring
    rw [he, movingSlotWeight_spectator_of_zero value childBound pivotBound _ extra
      (g i) (hg i) (D i) T t hT XL XR, ih]
    ring

/-- The complete moving coefficient splits into the original scalar support,
its actual smooth polynomial weight, and all of its spectator trees. No
nonzero-term hypothesis is needed. -/
theorem moving_full_smooth_spectator_of_zero {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : Polynomial ℝ) (z : ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (movingWindowLeaf value X lo hi F x s * movingFourierLeaf value ψ X x s) *
          ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (Dq i) x s)
        (movingSlotCutoff value childBound pivotBound
          (movingPhiExtra value childBound pivotBound extra φ G)) n ⟨n, T, XL, XR⟩ t =
      (recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
        n ⟨n, T, XL, XR⟩ t *
          smoothPolynomialWeight (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
            φ G B D hB hD hφ hlip) z) *
        ∏ i ∈ S, movingSlotSpectator value (g i) (Dq i) T XL XR := by
  rw [movingSlotWeight_spectator_product_of_zero q value childBound pivotBound _ _ g hg Dq S T t hT XL XR,
    moving_full_smooth_polynomial value hvalue childBound pivotBound F extra ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip hout T t hT hfreq XL XR L R z hL hR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWindowedSpectators
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete nonsmooth factor of the original moving coefficient -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- This identity includes all original arithmetic guards, terminal windows,
smooth factors, compensation weights, and spectators. -/
theorem moving_complete_coefficient_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (movingWindowLeaf value X lo hi (movingDataLeaf F) x s *
          movingFourierLeaf value ψ X x s) *
            ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (Dq i) x s)
        (movingSlotCutoff value childBound pivotBound
          (movingPhiExtra value childBound pivotBound (movingDataExtra E) φ G)) n ⟨n, T, XL, XR⟩ t =
      (movingArithmeticIndicator value childBound pivotBound T XL XR *
        movingWindowedSpectatorWeight q value F E X lo hi g Dq S T XL XR) *
          smoothPolynomialWeight (movingSmoothPolynomialFactors value T Polynomial.X (Polynomial.C XR)
            ψ X lo hi hlo hhi φ G B D hB hD hφ hlip) XL := by
  rw [moving_full_smooth_spectator_of_zero q value hvalue childBound pivotBound
    (movingDataLeaf F) (movingDataExtra E) g hg Dq S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    T t hT hf XL XR Polynomial.X (Polynomial.C XR) XL (by simp) (by simp)]
  rw [movingSlotWeight_indicator_factor value hvalue childBound pivotBound
    (movingWindowLeaf value X lo hi (movingDataLeaf F)) (movingDataExtra E) T t hT hf XL XR]
  unfold movingWindowedSpectatorWeight
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealWindows
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The terminal-window factor on two real giant coordinates -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotData.leafPolynomials_real {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (z : ℝ) (i : TreeLeafIndex n) :
    (T.leafPolynomials value L R i).eval z = T.realLeafModuli value (L.eval z) (R.eval z) i := by
  induction T generalizing L R with
  | leaf => simp only [leafPolynomials, realLeafModuli, Polynomial.eval_mul, Polynomial.eval_C]
  | node s CL CR U left right ihL ihR =>
    cases i with
    | inl i =>
      simpa only [leafPolynomials, realLeafModuli, MovingSlotReversal.pivotPolynomial_eval] using
        ihL ((MovingSlotData.step s CL CR U left right false).pivotPolynomial value L R) L i
    | inr i =>
      simpa only [leafPolynomials, realLeafModuli, MovingSlotReversal.pivotPolynomial_eval] using
        ihR ((MovingSlotData.step s CL CR U left right false).pivotPolynomial value L R) R i

theorem MovingSlotData.realLeafModuli_nat {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (hI : T.Integral value XL XR) (i : TreeLeafIndex n) :
    T.realLeafModuli value XL XR i = (T.leafModuli value XL XR i : ℝ) := by
  have h := T.leafPolynomials_real value Polynomial.X (Polynomial.C XR) XL i
  rw [T.leafPolynomials_eval value hvalue hf XL XR hI _ _ _ (by simp) (by simp) i] at h
  simpa only [Polynomial.eval_X, Polynomial.eval_C] using h.symm

theorem movingWindowedData_real_factor {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR) :
    movingUnrestrictedWeight value (movingWindowLeaf value X lo hi (movingDataLeaf F))
      (movingDataExtra E) T XL XR =
        movingRealWindowFlag value T X lo hi XL XR * movingDataWeight F E T := by
  rw [movingUnrestrictedWeight_data_window]
  simp only [movingRealWindowFlag, T.realLeafModuli_nat value hvalue hf XL XR hI]
  split_ifs <;> simp only [one_mul, zero_mul]

/-- The original nonsmooth coefficient is exactly a fixed residue factor
times a function of the two real giant coordinates. This includes zero terms. -/
theorem moving_original_nonsmooth_residue_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingArithmeticIndicator value childBound pivotBound T XL XR *
        movingWindowedSpectatorWeight q value F E X lo hi g D S T XL XR =
      (movingResidueFlag nodes (topGiantInput a b) * movingSpectatorResidue q value g D S T a b) *
        (movingArchimedeanFlag nodes (topGiantReal XL XR) *
          movingRealWindowFlag value T X lo hi XL XR * movingDataWeight F E T) := by
  dsimp only
  have he : movingArithmeticIndicator value childBound pivotBound T XL XR *
        movingWindowedSpectatorWeight q value F E X lo hi g D S T XL XR =
      (movingArithmeticIndicator value childBound pivotBound T XL XR *
        ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR) *
        (movingRealWindowFlag value T X lo hi XL XR * movingDataWeight F E T) := by
    by_cases hs : T.ArithmeticSupport value childBound pivotBound XL XR
    · unfold movingWindowedSpectatorWeight
      rw [movingWindowedData_real_factor value hvalue F E X lo hi T hf XL XR
        (hs.integral value hvalue childBound pivotBound T XL XR)]
      ring
    · have hz : movingArithmeticIndicator value childBound pivotBound T XL XR = 0 := ite_eq_right hs
      rw [hz, zero_mul, zero_mul, zero_mul]
  rw [he, moving_arithmetic_spectator_residue_factor q value hvalue childBound pivotBound
    g D S T hf XL XR a b M hM hMq hL hR]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCanonicalWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical residue coefficients of the original moving weight -/

namespace Ostmann
open scoped Classical BigOperators

theorem moving_original_canonical_coefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingArithmeticIndicator value childBound pivotBound T XL XR *
        movingWindowedSpectatorWeight q value F E X lo hi g D S T XL XR =
      movingResidueCoefficient q value F E g D S T nodes a b *
        movingRealGateWeight value T nodes X lo hi (topGiantReal XL XR) := by
  dsimp only
  rw [moving_original_nonsmooth_residue_factor q value hvalue childBound pivotBound F E
    X lo hi g D S T hf XL XR a b M hM hMq hL hR]
  simp only [movingResidueCoefficient, movingRealGateWeight, topGiantReal, Bool.false_eq_true,
    ite_false, if_false, ite_true, if_true]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealSmooth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single real smooth kernel for the two original giant coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem movingFourierPolynomialFactors_real {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (z : ℝ) :
    smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z =
      movingRealFourierWeight value T ψ X lo hi hlo hhi (L.eval z) (R.eval z) := by
  unfold smoothPolynomialWeight movingRealFourierWeight
  rw [← (movingLeafIndexEquiv n).prod_comp
    (fun j => (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi j).value z)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [movingFourierPolynomialFactors, Equiv.symm_apply_apply]
  split_ifs <;>
    simp only [ClippedPolynomialFactor.conjugate, ClippedPolynomialFactor.value,
      fourierPolynomialFactor, movingLeafNormalizedPolynomial_eval, T.leafPolynomials_real,
      Polynomial.eval_X]

theorem movingSmoothPolynomialFactors_real {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    smoothPolynomialWeight (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip) z =
        movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G (L.eval z) (R.eval z) := by
  rw [movingSmoothPolynomialFactors_value value T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout,
    movingFourierPolynomialFactors_real]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability and uniform bounds for the original two-giant kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap
open MeasureTheory

/-- The literal recursive coefficient, including all zero terms, is the
fixed residue coefficient times the single bounded real kernel. -/
theorem moving_recursive_real_kernel {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (movingWindowLeaf value X lo hi (movingDataLeaf F) x s *
          movingFourierLeaf value ψ X x s) *
            ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (Dq i) x s)
        (movingSlotCutoff value childBound pivotBound
          (movingPhiExtra value childBound pivotBound (movingDataExtra E) φ G)) n ⟨n, T, XL, XR⟩ t =
      movingResidueCoefficient q value F E g Dq S T nodes a b *
        movingRealKernel value T nodes ψ X lo hi hlo hhi φ G XL XR := by
  dsimp only
  rw [moving_complete_coefficient_factor q value hvalue childBound pivotBound F E g hg Dq S
    ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf XL XR,
    moving_original_canonical_coefficient q value hvalue childBound pivotBound F E X lo hi
      g Dq S T hf XL XR a b M hM hMq hL hR,
    movingSmoothPolynomialFactors_real value T Polynomial.X (Polynomial.C XR) ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip hout]
  simp only [Polynomial.eval_X, Polynomial.eval_C, movingRealKernel, mul_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalGiantWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A name for the literal original recursive giant coefficient -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap

theorem movingOriginalGiantWeight_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G T t XL XR =
      movingResidueCoefficient q value F E g Dq S T nodes a b *
        movingRealKernel value T nodes ψ X lo hi hlo hhi φ G XL XR :=
  moving_recursive_real_kernel q value hvalue childBound pivotBound F E g hg Dq S
    ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf XL XR a b M hM hMq hL hR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSupportedWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full manuscript support on the literal recursive giant weight -/

namespace Ostmann
open scoped Classical SchwartzMap

theorem movingOriginalGiantWeight_integral {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ)
    (hw : movingOriginalGiantWeight q value childBound pivotBound F E g Dq S
      ψ X lo hi φ G T t XL XR ≠ 0) : T.Integral value XL XR := by
  exact MovingSlotData.ArithmeticSupport.integral value hvalue childBound pivotBound T XL XR
    (movingSlotWeight_arithmeticSupport value hvalue childBound pivotBound _ _ T t hT hf XL XR hw)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DiagonalRegularMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual squared regular transform in the diagonal CRT average -/

namespace Ostmann
open scoped BigOperators Classical

theorem diagonalRegularMultiplier_local {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool)
    (s : ℤ) (other : ∀ i, ZMod (p i)) (hs : ∀ i, (s : ZMod (p i)) ≠ 0)
    (ho : ∀ i, other i ≠ 0) (g : ∀ i, ZMod (p i) → ℂ)
    (z : ∀ i, ZMod (p i) × (ZMod (p i))ˣ) :
    diagonalRegularMultiplier p active s other g z =
      ∏ i, externalRegularLocal (active i) (diagonalRegularCoefficient p s other hs ho i) (g i) (z i) := by
  by_cases hz : ∀ i, (z i).1 ≠ 0
  · rw [diagonalRegularMultiplier, ite_eq_left hz]
    apply Finset.prod_congr rfl
    intro i _
    rw [externalRegularLocal, ite_eq_right (hz i)]
    cases active i
    · rfl
    · simp only [ite_true, if_true, diagonalRegularCoefficient, Units.val_mk0,
        div_eq_mul_inv, mul_inv_rev]
      apply congrArg (fun x : ZMod (p i) => ‖g i x‖ ^ 2)
      ring
  · rw [diagonalRegularMultiplier, ite_eq_right hz]
    obtain ⟨i, hi⟩ := not_forall.mp hz
    have hiz : (z i).1 = 0 := not_ne_iff.mp hi
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [externalRegularLocal, hiz, ite_true, if_true]

/-- The manuscript's regular multiplier is integrated before taking any
absolute value of the signed remainder, which may include Page factors. -/
theorem diagonalRegularMultiplier_crt {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i))
    (hs : ∀ i, (s : ZMod (p i)) ≠ 0) (ho : ∀ i, other i ≠ 0)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (F : ZMod r × (ZMod r)ˣ → ℂ) :
    (Fintype.card (ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ) : ℂ)⁻¹ *
      (∑ z, (diagonalRegularMultiplier p active s other g
        (crtExternalPairEquiv p hc (crtSplitExternalEquiv (∏ i, p i) r hcop z).1) : ℂ) *
          F (crtSplitExternalEquiv (∏ i, p i) r hcop z).2) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ∑ z, F z) := by
  simp_rw [diagonalRegularMultiplier_local p active s other hs ho g]
  exact crt_external_regular_with_remainder p hc r hcop active
    (diagonalRegularCoefficient p s other hs ho) g hg henergy F

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RegularGiantMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The displayed regular-prime multiplier on actual natural giants -/

namespace Ostmann
open scoped BigOperators Classical

theorem guardedRegularMultiplier_modEq {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR YL YR M : ℕ)
    (hp : ∀ i, p i ∣ M) (hL : Nat.ModEq M XL YL) (hR : Nat.ModEq M XR YR) :
    guardedRegularMultiplier p active s other g XL XR = guardedRegularMultiplier p active s other g YL YR := by
  have hl (i : I) : (XL : ZMod (p i)) = (YL : ZMod (p i)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hL.of_dvd (hp i))
  have hr (i : I) : (XR : ZMod (p i)) = (YR : ZMod (p i)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hR.of_dvd (hp i))
  simp only [guardedRegularMultiplier, naturalRegularMultiplier, hl, hr]

theorem guardedRegularMultiplier_eq_diagonal {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ)
    (z : ∀ i, ZMod (p i) × (ZMod (p i))ˣ)
    (hL : ∀ i, (XL : ZMod (p i)) = (z i).1)
    (hR : ∀ i, (XR : ZMod (p i)) = ((z i).2 : ZMod (p i))) :
    guardedRegularMultiplier p active s other g XL XR = diagonalRegularMultiplier p active s other g z := by
  have hu (i : I) : ((z i).2 : ZMod (p i)) ≠ 0 := Units.ne_zero _
  have hguard : (∀ i, (z i).1 ≠ 0 ∧ ((z i).2 : ZMod (p i)) ≠ 0) ↔ ∀ i, (z i).1 ≠ 0 :=
    ⟨fun h i => (h i).1, fun h i => ⟨h i, hu i⟩⟩
  simp only [guardedRegularMultiplier, naturalRegularMultiplier, hL, hR, diagonalRegularMultiplier]
  simp only [hguard]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_GuardedRegularCRT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The displayed natural-giant regular multiplier in the CRT average -/

namespace Ostmann
open scoped BigOperators Classical

theorem regular_unit_tests_iff {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (XL XR : ℕ) :
    (∀ i, (XL : ZMod (p i)) ≠ 0 ∧ (XR : ZMod (p i)) ≠ 0) ↔
      XL.Coprime (∏ i, p i) ∧ XR.Coprime (∏ i, p i) := by
  simp only [← isUnit_iff_ne_zero, ZMod.isUnit_iff_coprime,
    Nat.coprime_prod_right_iff, Finset.mem_univ, forall_true_left, forall_and]

theorem guardedRegularMultiplier_eq_coprime {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ) :
    guardedRegularMultiplier p active s other g XL XR =
      if XL.Coprime (∏ i, p i) ∧ XR.Coprime (∏ i, p i) then
        naturalRegularMultiplier p active s other g XL XR else 0 := by
  simp only [guardedRegularMultiplier, regular_unit_tests_iff]

theorem multiply_regular_after_support {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ)
    (w c k : ℂ)
    (hw : w = if XL.Coprime XR ∧ XL.Coprime (∏ i, p i) ∧ XR.Coprime (∏ i, p i)
      then c * k else 0) :
    w * (naturalRegularMultiplier p active s other g XL XR : ℂ) =
      if XL.Coprime XR then (c * (guardedRegularMultiplier p active s other g XL XR : ℂ)) * k else 0 := by
  rw [hw, guardedRegularMultiplier_eq_coprime]
  by_cases hpair : XL.Coprime XR <;>
    by_cases hreg : XL.Coprime (∏ i, p i) ∧ XR.Coprime (∏ i, p i)
  · rw [ite_eq_left ⟨hpair, hreg⟩, ite_eq_left hreg, ite_eq_left hpair]
    ring
  · rw [ite_eq_right (fun h => hreg h.2), ite_eq_right hreg, ite_eq_left hpair]
    simp
  · rw [ite_eq_right (fun h => hpair h.1), ite_eq_right hpair]
    simp
  · rw [ite_eq_right (fun h => hpair h.1), ite_eq_right hpair]
    simp

theorem guardedRegularMultiplier_crt {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ)
    (z : ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ) :
    guardedRegularMultiplier p active s other g z.1.val (z.2 : ZMod ((∏ i, p i) * r)).val =
      diagonalRegularMultiplier p active s other g
        (crtExternalPairEquiv p hc (crtSplitExternalEquiv (∏ i, p i) r hcop z).1) := by
  apply guardedRegularMultiplier_eq_diagonal
  · intro i
    change (z.1.val : ZMod (p i)) =
      ZMod.prodEquivPi p hc ((ZMod.chineseRemainder hcop) z.1).1 i
    have h := congrArg (fun x : ZMod ((∏ i, p i) * r) =>
      ZMod.prodEquivPi p hc ((ZMod.chineseRemainder hcop) x).1 i)
      (ZMod.natCast_zmod_val z.1)
    simpa only [map_natCast, Prod.fst_natCast, Pi.natCast_apply] using h
  · intro i
    change ((z.2 : ZMod ((∏ i, p i) * r)).val : ZMod (p i)) =
      ZMod.prodEquivPi p hc ((ZMod.chineseRemainder hcop) (z.2 : ZMod ((∏ i, p i) * r))).1 i
    have h := congrArg (fun x : ZMod ((∏ i, p i) * r) =>
      ZMod.prodEquivPi p hc ((ZMod.chineseRemainder hcop) x).1 i)
      (ZMod.natCast_zmod_val (z.2 : ZMod ((∏ i, p i) * r)))
    simpa only [map_natCast, Prod.fst_natCast, Pi.natCast_apply] using h

/-- This is the actual natural-coordinate multiplier, not an auxiliary copy
of its transform. The remainder stays complex and may contain the Page factor. -/
theorem guardedRegularMultiplier_average {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i))
    (hs : ∀ i, (s : ZMod (p i)) ≠ 0) (ho : ∀ i, other i ≠ 0)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (F : ZMod r × (ZMod r)ˣ → ℂ) :
    (Fintype.card (ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ) : ℂ)⁻¹ *
      (∑ z, (guardedRegularMultiplier p active s other g z.1.val
        (z.2 : ZMod ((∏ i, p i) * r)).val : ℂ) *
          F (crtSplitExternalEquiv (∏ i, p i) r hcop z).2) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ∑ z, F z) := by
  simp_rw [guardedRegularMultiplier_crt p hc r hcop active s other g]
  exact diagonalRegularMultiplier_crt p hc r hcop active s other hs ho g hg henergy F

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAuxiliaryUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating inherited regular-slot units from the recursive residue tests -/

namespace Ostmann
open scoped Classical

theorem movingNaturalGiantUnits_auxiliary {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (h : movingNaturalGiantUnits value outside T XL XR) : movingAuxiliaryUnits value outside T XL XR := by
  induction T generalizing XL XR with
  | leaf => exact ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  | node s CL CR U left right ihL ihR =>
    exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2⟩,
      ihL _ _ h.2.1, ihR _ _ h.2.2⟩

private theorem localGiantUnits_of_pairwise {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hp : (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime)
    (hu : movingAuxiliaryLocalUnits outside T XL XR) : movingLocalGiantUnits value outside T XL XR := by
  have hcur : T.CurrentPairwise value XL XR := (List.pairwise_append.mp hp).1
  have h := (T.currentPairwise_iff value XL XR).mp hcur
  exact ⟨hu.1, hu.2.1, h.2.2.1.isCoprime, h.2.2.2.isCoprime, hu.2.2.1, hu.2.2.2⟩

theorem movingFullOutsidePairwise_giantUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hp : movingFullOutsidePairwise value outside T XL XR)
    (hu : movingAuxiliaryUnits value outside T XL XR) : movingNaturalGiantUnits value outside T XL XR := by
  induction T generalizing XL XR with
  | leaf => exact localGiantUnits_of_pairwise value outside _ _ _ hp hu
  | node s CL CR U left right ihL ihR =>
    exact ⟨localGiantUnits_of_pairwise value outside _ _ _ hp.1 hu.1,
      ihL _ _ hp.2.1 hu.2.1, ihR _ _ hp.2.2 hu.2.2⟩

theorem movingFullSupport_auxiliary_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    movingFullSupport value outside T XL XR ↔
      movingFullOutsidePairwise value outside T XL XR ∧ movingAuxiliaryUnits value outside T XL XR :=
  ⟨fun h => ⟨h.1, movingNaturalGiantUnits_auxiliary value outside T XL XR h.2⟩,
    fun h => ⟨h.1, movingFullOutsidePairwise_giantUnits value outside T XL XR h.1 h.2⟩⟩

private theorem currentOutsidePairwise_auxiliary_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hu : movingAuxiliaryLocalUnits outside T XL XR) :
    (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime ↔
      T.CurrentPairwise value XL XR ∧ (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
  have hXL := Nat.coprime_list_prod_right_iff.mp hu.2.2.1.natCoprime
  have hXR := Nat.coprime_list_prod_right_iff.mp hu.2.2.2.natCoprime
  simp only [MovingSlotData.currentSlots, MovingSlotData.CurrentPairwise,
    List.cons_append, List.pairwise_cons, List.mem_cons, List.mem_append, forall_eq_or_imp]
  constructor
  · rintro ⟨⟨hp, hl⟩, hr, hs⟩
    exact ⟨⟨⟨hp, fun a ha => hl a (Or.inl ha)⟩,
      (fun a ha => hr a (Or.inl ha)), (List.pairwise_append.mp hs).1⟩, hs⟩
  · rintro ⟨⟨⟨hp, hl⟩, hr, _⟩, hs⟩
    exact ⟨⟨hp, fun a ha => ha.elim (hl a) (hXL a)⟩,
      (fun a ha => ha.elim (hr a) (hXR a)), hs⟩

theorem movingFullOutsidePairwise_auxiliary_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hu : movingAuxiliaryUnits value outside T XL XR) :
    movingFullOutsidePairwise value outside T XL XR ↔
      T.FullPairwise value XL XR ∧ movingRegularOutsidePairwise value outside T := by
  induction T generalizing XL XR with
  | leaf => exact currentOutsidePairwise_auxiliary_iff value outside _ _ _ hu
  | node s CL CR U left right ihL ihR =>
    simp only [movingFullOutsidePairwise, MovingSlotData.FullPairwise,
      movingRegularOutsidePairwise, currentOutsidePairwise_auxiliary_iff value outside _ _ _ hu.1,
      ihL _ _ hu.2.1, ihR _ _ hu.2.2]
    tauto

private theorem naturalProduct_coprime_of_members {σ : Type*} (value : σ → ℕ) (s : ℤ)
    (L : List σ) (h : ∀ i ∈ L, IsCoprime s (value i : ℤ)) :
    IsCoprime s (MovingSlotReversal.naturalProduct value L : ℤ) := by
  induction L with
  | nil => simpa [MovingSlotReversal.naturalProduct] using (isCoprime_one_right (x := s))
  | cons a L ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons, Nat.cast_mul]
      using (h a List.mem_cons_self).mul_right (ih (fun i hi => h i (List.mem_cons_of_mem a hi)))

theorem movingAuxiliaryUnits_cross {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n)
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ))) (XL XR : ℕ)
    (hu : movingAuxiliaryUnits value outside T XL XR) : T.CrossFrequencyUnits value XL XR := by
  induction T generalizing XL XR with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    have hXL := (left.frequencies_isCoprime (XL : ℤ)).mpr
      (hu.1.1.of_isCoprime_of_dvd_right ⟨s * right.frequencyProduct, by
        simp only [MovingSlotData.frequencyProduct]; ring⟩)
    have hXR := (right.frequencies_isCoprime (XR : ℤ)).mpr
      (hu.1.2.1.of_isCoprime_of_dvd_right ⟨s * left.frequencyProduct, by
        simp only [MovingSlotData.frequencyProduct]; ring⟩)
    refine ⟨?_, ?_, ihL (fun i => (hsmall i).2.1) _ _ hu.2.1,
      ihR (fun i => (hsmall i).2.2) _ _ hu.2.2⟩
    · simpa only [Nat.cast_mul] using hXL.root.symm.mul_right
        (naturalProduct_coprime_of_members value left.frequency CL (fun i _ => (hsmall i).2.1.root))
    · simpa only [Nat.cast_mul] using hXR.root.symm.mul_right
        (naturalProduct_coprime_of_members value right.frequency CR (fun i _ => (hsmall i).2.2.root))

/-- All descendant regular-slot units have disappeared; only the top current
pair, the explicit square tests, and frequency/outside tests remain. -/
theorem movingFullSupport_auxiliary_square_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ))) (XL XR : ℕ)
    (hI : T.Integral value XL XR) :
    movingFullSupport value outside T XL XR ↔
      T.CurrentPairwise value XL XR ∧ movingRegularOutsidePairwise value outside T ∧
        T.PrimeSquareTests value XL XR ∧ movingAuxiliaryUnits value outside T XL XR := by
  rw [movingFullSupport_auxiliary_iff]
  constructor
  · rintro ⟨hp, hu⟩
    obtain ⟨hpair, hs⟩ := (movingFullOutsidePairwise_auxiliary_iff value outside T XL XR hu).mp hp
    obtain ⟨ht, hsq⟩ := (T.fullPairwise_iff_squareTests value hcoh hc XL XR hI
      (movingAuxiliaryUnits_cross value outside T hsmall XL XR hu)).mp hpair
    exact ⟨ht, hs, hsq, hu⟩
  · rintro ⟨ht, hs, hsq, hu⟩
    refine ⟨(movingFullOutsidePairwise_auxiliary_iff value outside T XL XR hu).mpr ⟨?_, hs⟩, hu⟩
    exact (T.fullPairwise_iff_squareTests value hcoh hc XL XR hI
      (movingAuxiliaryUnits_cross value outside T hsmall XL XR hu)).mpr ⟨ht, hsq⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAuxiliaryPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A residue period that omits inherited regular-slot unit tests -/

namespace Ostmann
open scoped Classical

theorem movingSignedAuxiliaryUnits_nat {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (hI : T.Integral value XL XR) :
    movingSignedAuxiliaryUnits value outside T XL XR ↔ movingAuxiliaryUnits value outside T XL XR := by
  induction T generalizing XL XR with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedAuxiliaryUnits, movingAuxiliaryUnits,
      (MovingSlotData.step s CL CR U left right false).signedPivot_nat value hvalue hf.1 XL XR hI.1,
      ihL hf.2.1 _ _ hI.2.1, ihR hf.2.2 _ _ hI.2.2]

theorem movingAuxiliaryLocalUnits_modEq {σ : Type*} (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR YL YR : ℤ)
    (hL : XL ≡ YL [ZMOD T.frequencyProduct * outside.prod])
    (hR : XR ≡ YR [ZMOD T.frequencyProduct * outside.prod]) :
    movingAuxiliaryLocalUnits outside T XL XR ↔ movingAuxiliaryLocalUnits outside T YL YR := by
  unfold movingAuxiliaryLocalUnits
  rw [int_modEq_isCoprime_iff (hL.of_dvd (dvd_mul_right _ _)),
    int_modEq_isCoprime_iff (hR.of_dvd (dvd_mul_right _ _)),
    int_modEq_isCoprime_iff (hL.of_dvd (dvd_mul_left _ _)),
    int_modEq_isCoprime_iff (hR.of_dvd (dvd_mul_left _ _))]

theorem movingSignedAuxiliaryUnits_modEq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR YL YR : ℤ)
    (hL : XL ≡ YL [ZMOD movingAuxiliaryUnitPeriod value outside T])
    (hR : XR ≡ YR [ZMOD movingAuxiliaryUnitPeriod value outside T]) :
    movingSignedAuxiliaryUnits value outside T XL XR ↔ movingSignedAuxiliaryUnits value outside T YL YR := by
  induction T generalizing XL XR YL YR with
  | leaf s regular => exact movingAuxiliaryLocalUnits_modEq outside _ _ _ _ _ hL hR
  | node s CL CR U left right ihL ihR =>
    let T := MovingSlotData.node s CL CR U left right
    let a := T.frequencyProduct * (outside.prod : ℤ)
    let c := s * (MovingSlotReversal.naturalProduct value U : ℤ)
    let dl := movingAuxiliaryUnitPeriod value outside left
    let dr := movingAuxiliaryUnitPeriod value outside right
    have hd : movingAuxiliaryUnitPeriod value outside T = a * c * dl * dr := rfl
    have hl : movingAuxiliaryLocalUnits outside T XL XR ↔ movingAuxiliaryLocalUnits outside T YL YR :=
      movingAuxiliaryLocalUnits_modEq outside T XL XR YL YR
        (hL.of_dvd ⟨c * dl * dr, by rw [hd]; ring⟩)
        (hR.of_dvd ⟨c * dl * dr, by rw [hd]; ring⟩)
    let step := MovingSlotData.step s CL CR U left right false
    let p := step.signedPivot value XL XR
    let r := step.signedPivot value YL YR
    have hp : p ≡ r [ZMOD a * dl * dr] :=
      step.signedPivot_modEq value hvalue hf.1 XL XR YL YR _
        (hL.of_dvd ⟨1, by change a * c * dl * dr = c * (a * dl * dr) * 1; ring⟩)
        (hR.of_dvd ⟨1, by change a * c * dl * dr = c * (a * dl * dr) * 1; ring⟩)
    exact and_congr hl (and_congr
      (ihL hf.2.1 p XL r YL (hp.of_dvd ⟨a * dr, by ring⟩)
        (hL.of_dvd ⟨a * c * dr, by rw [hd]; ring⟩))
      (ihR hf.2.2 p XR r YR (hp.of_dvd ⟨a * dl, by ring⟩)
        (hR.of_dvd ⟨a * c * dl, by rw [hd]; ring⟩)))

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

theorem small_prime_frequency_unit (p : ℕ) (hp : p.Prime) (s : ℤ)
    (hs : s ≠ 0) (hsp : s.natAbs < p) : IsCoprime s (p : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]
  exact (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hs) hsp)).symm

theorem MovingSlotData.small_frequency_units {σ : Type*} (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (V : ℕ) (hlarge : ∀ i, V < value i)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hV : T.Frequencies (fun s => s.natAbs ≤ V)) :
    ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)) := by
  intro i
  induction T with
  | leaf s regular => exact small_prime_frequency_unit (value i) (hprime i) s hf (hV.trans_lt (hlarge i))
  | node s CL CR U left right ihL ihR =>
    exact ⟨small_prime_frequency_unit (value i) (hprime i) s hf.1 (hV.1.trans_lt (hlarge i)),
      ihL hf.2.1 hV.2.1, ihR hf.2.2 hV.2.2⟩

theorem MovingSlotData.small_frequency_residues {σ : Type*} (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (V : ℕ) (hlarge : ∀ i, V < value i)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hV : T.Frequencies (fun s => s.natAbs ≤ V)) :
    ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0) := by
  intro i
  let : Fact (value i).Prime := ⟨hprime i⟩
  apply (T.small_frequency_units value hprime V hlarge hf hV i).mono
  intro s hs
  have hu : IsUnit (s : ZMod (value i)) := by
    apply isCoprime_zero_right.mp
    simpa only [Int.cast_natCast, ZMod.natCast_self] using hs.intCast (R := ZMod (value i))
  exact hu.ne_zero

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingReducedSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive residue support after extracting the regular-prime units -/

namespace Ostmann
open scoped Classical

theorem movingReducedResidueSupport_modEq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR YL YR M : ℤ)
    (hunit : movingAuxiliaryUnitPeriod value outside T ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    movingReducedResidueSupport value outside T XL XR ↔
      movingReducedResidueSupport value outside T YL YR := by
  unfold movingReducedResidueSupport
  rw [movingSquareLineSupport_modEq value T XL XR YL YR M hsquare hL hR,
    movingSignedAuxiliaryUnits_modEq value hvalue outside T hf XL XR YL YR
      (hL.of_dvd hunit) (hR.of_dvd hunit)]

theorem movingFullSupport_reduced_iff {σ : Type*} (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR) :
    movingFullSupport value outside T XL XR ↔
      XL.Coprime XR ∧
      XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
      XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
      movingReducedResidueSupport value outside T XL XR := by
  rw [movingFullSupport_auxiliary_square_iff value outside T hcoh hc hsmall XL XR hI,
    T.currentPairwise_iff value XL XR,
    T.squareTests_iff_lines tier value hprime hdisjoint hlevels hfmod XL XR hI,
    ← movingSignedAuxiliaryUnits_nat value (fun i => (hprime i).ne_zero) outside T hf XL XR hI]
  have hstatic : movingRegularOutsidePairwise value outside T →
      (T.regularSlots.map value).Pairwise Nat.Coprime := by
    intro h
    have hr : (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
      cases T with
      | leaf => exact h
      | node => exact h.1
    exact (List.pairwise_append.mp hr).1
  simp only [movingReducedResidueSupport, movingSquareLineSupport, Int.cast_natCast]
  tauto

theorem movingSupportedWeight_reduced_residue {σ : Type*} (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR a b : ℕ) (M : ℤ) (z : ℂ) (hI : z ≠ 0 → T.Integral value XL XR)
    (hunit : movingAuxiliaryUnitPeriod value outside T ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    movingSupportedWeight value outside T XL XR z =
      if XL.Coprime XR ∧
          XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
          XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) then
        movingReducedResidueWeight value outside T a b z else 0 := by
  by_cases hz : z = 0
  · simp [movingSupportedWeight, movingReducedResidueWeight, hz]
  · have hs := movingFullSupport_reduced_iff tier value hprime hdisjoint outside T hlevels hcoh hc
      hf hsmall hfmod XL XR (hI hz)
    rw [movingReducedResidueSupport_modEq value (fun i => (hprime i).ne_zero) outside T hf
      XL XR a b M hunit hsquare hL hR] at hs
    unfold movingSupportedWeight movingReducedResidueWeight
    rw [hs]
    split_ifs <;> simp_all

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSpectatorModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete modulus for arithmetic support and all spectator trees -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTopPeriod_dvd_spectatorModulus {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (q : I → ℕ) (S : Finset I) :
    movingTopPeriod value hvalue childBound pivotBound T hf ∣
      movingSpectatorModulus value hvalue childBound pivotBound T hf q S := by
  exact ⟨(movingSpectatorDenominator value T).natAbs * ∏ i ∈ S, q i, by
    simp only [movingSpectatorModulus, mul_assoc]⟩

theorem spectator_dvd_movingSpectatorModulus {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (q : I → ℕ) (S : Finset I)
    (i : I) (hi : i ∈ S) :
    (q i : ℤ) * movingSpectatorDenominator value T ∣
      (movingSpectatorModulus value hvalue childBound pivotBound T hf q S : ℤ) := by
  obtain ⟨z, hz⟩ := Int.dvd_natAbs.mpr (dvd_refl (movingSpectatorDenominator value T))
  obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem q hi
  refine ⟨(movingTopPeriod value hvalue childBound pivotBound T hf : ℤ) * z * w, ?_⟩
  simp only [movingSpectatorModulus, Nat.cast_mul, hz, hw]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFullModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete common modulus for every full-support residue test -/

namespace Ostmann
open scoped BigOperators Classical

theorem MovingSlotData.compensation_dvd_spectatorDenominator {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) :
    ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
      (value i : ℤ) ∣ movingSpectatorDenominator value T := by
  induction T with
  | leaf => simp [occurrences]
  | node s CL CR U left right ihL ihR =>
    intro o ho i hi
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      have hd : value i ∣ MovingSlotReversal.naturalProduct value U :=
        List.dvd_prod (List.mem_map.mpr ⟨i, hi, rfl⟩)
      have hz : (value i : ℤ) ∣ (MovingSlotReversal.naturalProduct value U : ℤ) := by exact_mod_cast hd
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hz s) _) _
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (ihL o' ho' i hi) _) _
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        exact dvd_mul_of_dvd_right (ihR o' ho' i hi) _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingReducedModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common residue modulus after extracting the regular primes -/

namespace Ostmann
open scoped BigOperators Classical

theorem movingReducedPairModulus_components {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) (b : Bool) :
    movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S ∣
      movingReducedPairModulusBase value hvalue outside childBound pivotBound T hf q S ∧
    (movingAuxiliaryUnitPeriod value outside (T b)).natAbs ∣
      movingReducedPairModulusBase value hvalue outside childBound pivotBound T hf q S := by
  have h := Finset.dvd_prod_of_mem
    (fun b => movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S *
      (movingAuxiliaryUnitPeriod value outside (T b)).natAbs) (Finset.mem_univ b)
  exact ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩

/-- The one common modulus supplies all four divisibility conditions used in
exact two-history factorization, including every compensation-prime square. -/
theorem movingReducedPairModulus_tests {σ I : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (q : I → ℕ) (S : Finset I) :
    let M := movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S
    (∀ b, movingTopPeriod value hvalue childBound pivotBound (T b) (hf b) ∣ M) ∧
    (∀ b, ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value (T b) ∣ (M : ℤ)) ∧
    (∀ b, movingAuxiliaryUnitPeriod value outside (T b) ∣ (M : ℤ)) ∧
    (∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ)) := by
  let N := movingReducedPairModulusBase value hvalue outside childBound pivotBound T hf q S
  have hN : N ∣ N ^ 2 := ⟨N, pow_two N⟩
  have hc := movingReducedPairModulus_components value hvalue outside childBound pivotBound T hf q S
  have hs (b : Bool) : movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S ∣ N ^ 2 :=
    (hc b).1.trans hN
  refine ⟨fun b => (movingTopPeriod_dvd_spectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S).trans (hs b),
    fun b i hi => ?_, fun b => ?_, fun b o ho i hi => ?_⟩
  · exact (spectator_dvd_movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S i hi).trans
      (by exact_mod_cast hs b)
  · exact (Int.dvd_natAbs.mpr (dvd_refl (movingAuxiliaryUnitPeriod value outside (T b)))).trans
      (by exact_mod_cast (hc b).2.trans hN)
  · have hd : value i ∣ (movingSpectatorDenominator value (T b)).natAbs := by
      exact_mod_cast Int.dvd_natAbs.mpr ((T b).compensation_dvd_spectatorDenominator value o ho i hi)
    have hds : (movingSpectatorDenominator value (T b)).natAbs ∣
        movingSpectatorModulus value hvalue childBound pivotBound (T b) (hf b) q S := by
      refine ⟨movingTopPeriod value hvalue childBound pivotBound (T b) (hf b) * ∏ j ∈ S, q j, ?_⟩
      simp only [movingSpectatorModulus]
      ring
    have hpow := pow_dvd_pow_of_dvd (hd.trans (hds.trans (hc b).1)) 2
    exact_mod_cast hpow

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingReducedWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original-weight factorization with the regular units extracted -/

namespace Ostmann
open scoped Classical SchwartzMap

theorem movingOriginalGiantWeight_reduced_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hlevels : T.Levels tier) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR a b M : ℕ)
    (hM : movingTopPeriod value (fun i => (hprime i).ne_zero) childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hunit : movingAuxiliaryUnitPeriod value outside T ∣ (M : ℤ))
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound hf (.prime false) (.prime true)
    movingSupportedWeight value outside T XL XR
      (movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G T t XL XR) =
      if XL.Coprime XR ∧
          XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
          XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) then
        movingReducedResidueWeight value outside T a b
          (movingResidueCoefficient q value F E g Dq S T nodes a b) *
            movingRealKernel value T nodes ψ X lo hi hlo hhi φ G XL XR else 0 := by
  dsimp only
  have hvalue : ∀ i, value i ≠ 0 := fun i => (hprime i).ne_zero
  rw [movingSupportedWeight_reduced_residue tier value hprime hdisjoint outside T hlevels hcoh hc hf
    hsmall hfmod XL XR a b M _
    (movingOriginalGiantWeight_integral q value hvalue childBound pivotBound F E g Dq S
      ψ X lo hi φ G T t hT hf XL XR) hunit hsquare hL hR,
    movingOriginalGiantWeight_factor q value hvalue childBound pivotBound F E g hg Dq S
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf XL XR a b M hM hMq hL hR]
  split_ifs
  · unfold movingReducedResidueWeight
    split_ifs <;> simp
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingReducedCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Periodicity of the remaining arithmetic and spectator coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingResidueGate_modEq (nodes : List MovingFormulaNode) (x y : Bool → ℤ) (M : ℕ)
    (hM : movingArithmeticPeriod nodes ∣ M) (hxy : ∀ i, x i ≡ y i [ZMOD M]) :
    movingResidueGate nodes x ↔ movingResidueGate nodes y := by
  apply forall₂_congr
  intro f hf
  apply and_congr_left
  intro _
  exact f.residueTests_modEq x y (fun i => (hxy i).of_dvd
    (by exact_mod_cast (movingArithmeticPeriod_dvd nodes f hf).trans hM))

theorem movingResidueCoefficient_modEq {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (a b c d M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (a : ℤ) ≡ (c : ℤ) [ZMOD M]) (hR : (b : ℤ) ≡ (d : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingResidueCoefficient q value F E g D S T nodes a b =
      movingResidueCoefficient q value F E g D S T nodes c d := by
  dsimp only
  have hgates := movingResidueGate_modEq _ (topGiantInput a b) (topGiantInput c d) M hM
    (by intro i; cases i; exact hL; exact hR)
  have hs : movingSpectatorResidue q value g D S T a b = movingSpectatorResidue q value g D S T c d := by
    apply Finset.prod_congr rfl
    intro i hi
    exact movingSignedSpectator_modEq value hvalue (g i) (D i) T hf a b c d
      (hL.of_dvd (hMq i hi)) (hR.of_dvd (hMq i hi))
  simp only [movingResidueCoefficient, movingResidueFlag, hgates, hs]

theorem movingReducedResidueWeight_modEq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (a b c d : ℤ) (M : ℤ) (z w : ℂ)
    (hunit : movingAuxiliaryUnitPeriod value outside T ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : a ≡ c [ZMOD M]) (hR : b ≡ d [ZMOD M]) (hz : z = w) :
    movingReducedResidueWeight value outside T a b z = movingReducedResidueWeight value outside T c d w := by
  simp only [movingReducedResidueWeight, hz,
    movingReducedResidueSupport_modEq value hvalue outside T hf a b c d M hunit hsquare hL hR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingReducedPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original histories with a common regular-prime block extracted -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem movingOriginalGiantWeight_reduced_pair_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (t : Bool → FrequencyTree ℤ n)
    (hT : ∀ b, (T b).Follows (t b)) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hlevels : ∀ b, (T b).Levels tier) (hcoh : ∀ b, (T b).RegularCoherent)
    (hc : ∀ b, (T b).CompensationPrimeData value)
    (hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ b i, (T b).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (R : ℕ) (hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = R)
    (XL XR a b M : ℕ)
    (hM : ∀ b, movingTopPeriod value (fun i => (hprime i).ne_zero) childBound pivotBound (T b) (hf b) ∣ M)
    (hMq : ∀ b, ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value (T b) ∣ (M : ℤ))
    (hunit : ∀ b, movingAuxiliaryUnitPeriod value outside (T b) ∣ (M : ℤ))
    (hsquare : ∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
    let c := fun side => movingReducedResidueWeight value outside (T side) a b
      (movingResidueCoefficient q value (F side) (E side) g (Dq side) S (T side) (nodes side) a b)
    movingSupportedWeight value outside (T false) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (F false) (E false) g (Dq false) S
        ψ X lo hi φ G (T false) (t false) XL XR) *
      conj (movingSupportedWeight value outside (T true) XL XR
        (movingOriginalGiantWeight q value childBound pivotBound (F true) (E true) g (Dq true) S
          ψ X lo hi φ G (T true) (t true) XL XR)) =
      if XL.Coprime XR ∧ XL.Coprime R ∧ XR.Coprime R then (c false * conj (c true)) *
        movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G XL XR else 0 := by
  dsimp only
  rw [movingOriginalGiantWeight_reduced_factor q tier value hprime hdisjoint outside childBound pivotBound
    (F false) (E false) g hg (Dq false) S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    (T false) (t false) (hT false) (hlevels false) (hcoh false) (hc false) (hf false)
    (hsmall false) (hfmod false) XL XR a b M (hM false) (hMq false) (hunit false) (hsquare false) hL hR,
    movingOriginalGiantWeight_reduced_factor q tier value hprime hdisjoint outside childBound pivotBound
    (F true) (E true) g hg (Dq true) S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    (T true) (t true) (hT true) (hlevels true) (hcoh true) (hc true) (hf true)
    (hsmall true) (hfmod true) XL XR a b M (hM true) (hMq true) (hunit true) (hsquare true) hL hR]
  simp only [hregular]
  by_cases hp : XL.Coprime XR ∧ XL.Coprime R ∧ XR.Coprime R
  · rw [ite_eq_left hp, ite_eq_left hp, ite_eq_left hp, map_mul, movingRealKernelPair]
    ring
  · rw [ite_eq_right hp, ite_eq_right hp, ite_eq_right hp, map_zero, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingReducedOuterFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original outer priors with the regular block removed from the residue coefficient -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem movingOriginalSupportedOuterPair_reduced_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (t : Bool → FrequencyTree ℤ n)
    (hT : ∀ b, (T b).Follows (t b)) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hlevels : ∀ b, (T b).Levels tier) (hcoh : ∀ b, (T b).RegularCoherent)
    (hc : ∀ b, (T b).CompensationPrimeData value)
    (hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ b i, (T b).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (R : ℕ) (hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = R)
    (XL XR : ℕ) :
    let hv := fun i => (hprime i).ne_zero
    let M := movingReducedPairModulus value hv outside childBound pivotBound T hf q S
    let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
    let c := movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes
    movingOriginalSupportedOuterPair q value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t XL XR =
      if XL.Coprime XR ∧ XL.Coprime R ∧ XR.Coprime R then c (XL % M) (XR % M) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal XL XR else 0 := by
  dsimp only
  let hv := fun i => (hprime i).ne_zero
  let M := movingReducedPairModulus value hv outside childBound pivotBound T hf q S
  have ht := movingReducedPairModulus_tests value hv outside childBound pivotBound T hf q S
  have h := movingOriginalGiantWeight_reduced_pair_factor q tier value hprime hdisjoint outside childBound pivotBound
    F E g hg Dq S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf hlevels hcoh hc hsmall hfmod
    R hregular XL XR (XL % M) (XR % M) M ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XL M).symm)
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XR M).symm)
  dsimp only [movingOriginalSupportedOuterPair]
  rw [h]
  by_cases hp : XL.Coprime XR ∧ XL.Coprime R ∧ XR.Coprime R
  · rw [ite_eq_left hp, ite_eq_left hp]
    exact mul_assoc _ _ _
  · rw [ite_eq_right hp, ite_eq_right hp, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageConductorProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected Page correction factors through the frequency modulus -/

namespace Ostmann

open Classical

/-- The character value itself depends only on the smaller residue. This
is the arithmetic justification for keeping the Page factor in the
frequency-coordinate average when applying CRT. -/
theorem pageCoefficient_eq_of_modEq (z : Option PrimitiveRealZero) {Q a b : ℕ}
    (hab : Nat.ModEq Q a b) :
    pageCoefficient (pageAtModulus Q z) a = pageCoefficient (pageAtModulus Q z) b := by
  cases z with
  | none => rfl
  | some e =>
    by_cases hd : e.modulus ∣ Q
    · have heq : (a : ZMod e.modulus) = (b : ZMod e.modulus) :=
        (ZMod.natCast_eq_natCast_iff a b e.modulus).mpr (hab.of_dvd hd)
      simp only [pageAtModulus, Option.bind_some, ite_eq_left hd, pageCoefficient, heq]
    · simp [pageAtModulus, hd, pageCoefficient]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageResidueReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the Page factor when redundant residue coordinates are removed -/

namespace Ostmann
open scoped BigOperators Classical

theorem nat_modEq_castHom_val {m n : ℕ} [NeZero m] [NeZero n]
    (h : m ∣ n) (a : ZMod n) :
    Nat.ModEq m a.val ((ZMod.castHom h (ZMod m)) a).val := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [ZMod.natCast_zmod_val]
  have hh := map_natCast (ZMod.castHom h (ZMod m)) a.val
  rw [ZMod.natCast_zmod_val] at hh
  exact hh.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingReducedCRT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original reduced arithmetic coefficient in the regular-prime CRT split -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem crtSplitExternalEquiv_snd (c r : ℕ) (hcop : c.Coprime r)
    (z : ZMod (c * r) × (ZMod (c * r))ˣ) :
    (crtSplitExternalEquiv c r hcop z).2 = externalResidueReduction (dvd_mul_left r c) z := by
  have he (a : ZMod (c * r)) : (ZMod.chineseRemainder hcop a).2 =
      ZMod.castHom (dvd_mul_left r c) (ZMod r) a :=
    RingHom.congr_fun (Subsingleton.elim
      ((RingHom.snd (ZMod c) (ZMod r)).comp (ZMod.chineseRemainder hcop).toRingHom)
      (ZMod.castHom (dvd_mul_left r c) (ZMod r))) a
  apply Prod.ext
  · exact he z.1
  · apply Units.ext
    exact he (z.2 : ZMod (c * r))

theorem movingReducedPairResidueCoefficient_modEq {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (a b c d : ℕ)
    (hL : (a : ℤ) ≡ (c : ℤ) [ZMOD movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S])
    (hR : (b : ℤ) ≡ (d : ℤ) [ZMOD movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S]) :
    let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
    movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes a b =
      movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes c d := by
  dsimp only
  have ht := movingReducedPairModulus_tests value hvalue outside childBound pivotBound T hf q S
  have he (side : Bool) := movingReducedResidueWeight_modEq value hvalue outside (T side) (hf side)
    a b c d _ _ _ (ht.2.2.1 side) (ht.2.2.2 side) hL hR
    (movingResidueCoefficient_modEq q value hvalue childBound pivotBound (F side) (E side)
      g (Dq side) S (T side) (hf side) a b c d _ (ht.1 side) (ht.2.1 side) hL hR)
  exact congrArg₂ (fun x y : ℂ => x * conj y) (he false) (he true)

/-- A periodic natural-coordinate coefficient descends to the second CRT
coordinate without changing its signed value. -/
theorem periodic_coefficient_crt (C : ℕ → ℕ → ℂ) (c r : ℕ) [NeZero r] [NeZero (c * r)]
    (hcop : c.Coprime r)
    (hC : ∀ a b d e, Nat.ModEq r a d → Nat.ModEq r b e → C a b = C d e)
    (z : ZMod (c * r) × (ZMod (c * r))ˣ) :
    C z.1.val (z.2 : ZMod (c * r)).val =
      C (crtSplitExternalEquiv c r hcop z).2.1.val
        ((crtSplitExternalEquiv c r hcop z).2.2 : ZMod r).val := by
  rw [crtSplitExternalEquiv_snd]
  apply hC
  · exact nat_modEq_castHom_val (dvd_mul_left r c) z.1
  · exact nat_modEq_castHom_val (dvd_mul_left r c) (z.2 : ZMod (c * r))

/-- Both factors are evaluated at their original natural residue representatives.
Only periodicity and the proved local transform energy are used in the split. -/
theorem periodic_coefficient_regular_average {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i))
    (hs : ∀ i, (s : ZMod (p i)) ≠ 0) (ho : ∀ i, other i ≠ 0)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (C : ℕ → ℕ → ℂ)
    (hC : ∀ a b d e, Nat.ModEq r a d → Nat.ModEq r b e → C a b = C d e) :
    (Fintype.card (ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ) : ℂ)⁻¹ *
      (∑ z : ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ, (guardedRegularMultiplier p active s other g z.1.val
        (z.2 : ZMod ((∏ i, p i) * r)).val : ℂ) * C z.1.val (z.2 : ZMod ((∏ i, p i) * r)).val) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ∑ z : ZMod r × (ZMod r)ˣ, C z.1.val (z.2 : ZMod r).val) := by
  simp_rw [periodic_coefficient_crt C (∏ i, p i) r hcop hC]
  exact guardedRegularMultiplier_average p hc r hcop active s other hs ho g hg henergy
    (fun z => C z.1.val (z.2 : ZMod r).val)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationLines
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compensation divisibility is the current internal-prime line condition

The equivalence below is used before imposing integrality of the new giant.
Thus the line condition recovers the original compensation division instead
of merely being a consequence of an already integral history.
-/

namespace Ostmann
open scoped Classical

theorem pairwise_coprime_list_prod_dvd_iff (U : List ℕ)
    (hU : U.Pairwise Nat.Coprime) (Q : ℕ) :
    U.prod ∣ Q ↔ ∀ b ∈ U, b ∣ Q := by
  constructor
  · intro h b hb
    exact (List.dvd_prod hb).trans h
  · induction U with
    | nil => simp
    | cons b U ih =>
      intro h
      obtain ⟨hbU, hUU⟩ := List.pairwise_cons.mp hU
      have hb := h b (by simp)
      have ht := ih hUU (fun c hc => h c (List.mem_cons_of_mem b hc))
      exact (Nat.coprime_list_prod_right_iff.mpr hbU).mul_dvd_of_dvd_of_dvd hb ht

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency residues with compensation factors inverted

Unlike the signed integer recursion, this recursion divides only by the
frequency. Compensation factors are inverted modulo a frequency power, so
no internal prime enters its period. One power is consumed per reversal.
-/

namespace Ostmann
open scoped Classical

theorem coprime_bezout_inverse_modEq (u R : ℤ) (hu : IsCoprime u R) (k : ℕ) :
    u * Int.gcdA u (R ^ k) ≡ 1 [ZMOD R ^ k] := by
  have h := Int.gcd_eq_gcd_ab u (R ^ k)
  have hg : Int.gcd u (R ^ k) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hu.pow_right
  rw [hg] at h
  apply Int.modEq_iff_dvd.mpr
  refine ⟨Int.gcdB u (R ^ k), ?_⟩
  linear_combination h

theorem MovingSlotReversal.signedNumerator_modEq {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (XL XR YL YR M : ℤ)
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    s.signedNumerator value XL XR ≡ s.signedNumerator value YL YR [ZMOD M] :=
  ((hR.mul_right _).mul_left _).sub ((hL.mul_right _).mul_left _)

theorem MovingSlotReversal.frequencyPivot_modEq {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (R : ℤ) (k : ℕ) (hs : s.rootFrequency ≠ 0)
    (hsR : s.rootFrequency ∣ R) (XL XR YL YR : ℤ)
    (hL : XL ≡ YL [ZMOD R ^ (k + 1)]) (hR : XR ≡ YR [ZMOD R ^ (k + 1)]) :
    s.frequencyPivot value R k XL XR ≡ s.frequencyPivot value R k YL YR [ZMOD R ^ k] := by
  have hd : s.rootFrequency * R ^ k ∣ R ^ (k + 1) := by
    simpa only [pow_succ, mul_comm] using mul_dvd_mul hsR (dvd_refl (R ^ k))
  exact (int_modEq_ediv _ _ _ _ hs
    ((s.signedNumerator_modEq value XL XR YL YR _ hL hR).of_dvd hd)).mul_right _

theorem movingFrequencyLocalUnits_modEq {σ : Type*} {n : ℕ} (T : MovingSlotData σ n)
    (XL XR YL YR M : ℤ) (hM : T.frequencyProduct ∣ M)
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    movingFrequencyLocalUnits T XL XR ↔ movingFrequencyLocalUnits T YL YR := by
  exact and_congr (int_modEq_isCoprime_iff (hL.of_dvd hM))
    (int_modEq_isCoprime_iff (hR.of_dvd hM))

theorem MovingSlotData.frequencyProduct_node_dvd {σ : Type*} {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n) (R : ℤ)
    (h : (MovingSlotData.node s CL CR U left right).frequencyProduct ∣ R) :
    s ∣ R ∧ left.frequencyProduct ∣ R ∧ right.frequencyProduct ∣ R := by
  refine ⟨?_, ?_, ?_⟩
  · exact dvd_trans ⟨left.frequencyProduct * right.frequencyProduct, by
      simp only [frequencyProduct]; ring⟩ h
  · exact dvd_trans ⟨s * right.frequencyProduct, by
      simp only [frequencyProduct]; ring⟩ h
  · exact (dvd_mul_left _ _).trans h

/-- The entire frequency block has a period containing only frequencies.
The compensation primes have disappeared from the period. -/
theorem movingFrequencyGate_modEq {σ : Type*} (value : σ → ℕ) (R : ℤ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hR : T.frequencyProduct ∣ R) (XL XR YL YR : ℤ)
    (hL : XL ≡ YL [ZMOD R ^ (n + 1)]) (hRight : XR ≡ YR [ZMOD R ^ (n + 1)]) :
    movingFrequencyGate value R T XL XR ↔ movingFrequencyGate value R T YL YR := by
  induction T generalizing XL XR YL YR with
  | leaf s regular =>
    exact movingFrequencyLocalUnits_modEq _ _ _ _ _ _
      (by simpa using hR) hL hRight
  | @node n s CL CR U left right ihL ihR =>
    have hd := MovingSlotData.frequencyProduct_node_dvd s CL CR U left right R hR
    have hp := (MovingSlotData.step s CL CR U left right false).frequencyPivot_modEq
      value R (n + 1) hf.1 hd.1 XL XR YL YR hL hRight
    have hpow : R ∣ R ^ (n + 1 + 1) := dvd_pow_self R (by omega)
    have hnum := (MovingSlotData.step s CL CR U left right false).signedNumerator_modEq
      value XL XR YL YR _ hL hRight
    have hdiv : s ∣ (MovingSlotData.step s CL CR U left right false).signedNumerator value XL XR ↔
        s ∣ (MovingSlotData.step s CL CR U left right false).signedNumerator value YL YR :=
      (hnum.of_dvd (hd.1.trans hpow)).dvd_iff
    have hlocal := movingFrequencyLocalUnits_modEq
      (MovingSlotData.node s CL CR U left right) XL XR YL YR _ (hR.trans hpow) hL hRight
    change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
    exact and_congr hlocal (and_congr hdiv (and_congr
      (ihL hf.2.1 hd.2.1 _ _ _ _ hp (hL.of_dvd (pow_dvd_pow R (by omega))))
      (ihR hf.2.2 hd.2.2 _ _ _ _ hp (hRight.of_dvd (pow_dvd_pow R (by omega))))))

theorem movingNaturalProduct_coprime {σ : Type*} (value : σ → ℕ) (slots : List σ)
    (R : ℤ) (h : ∀ i ∈ slots, IsCoprime (value i : ℤ) R) :
    IsCoprime (MovingSlotReversal.naturalProduct value slots : ℤ) R := by
  induction slots with
  | nil => simpa [MovingSlotReversal.naturalProduct] using (isCoprime_one_left (x := R))
  | cons i slots ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons, Nat.cast_mul] using
      (h i List.mem_cons_self).mul_left (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLineComposition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Composition of the cleared occurrence lines

The identity works before any descendant division. It lets the current
internal-prime congruence establish integrality inductively, without assuming
the conclusion for the rest of the path.
-/

namespace Ostmann
open scoped Classical

theorem PolynomialGiantRows.evalNumerator_movingReverse {σ R : Type*} [CommRing R]
    (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* R)
    (left : Bool) (v w u : MvPolynomial σ ℤ) (x y : R) :
    (T.movingReverse left v w u).evalNumerator φ x y =
      (φ v * (T.evalNumerator φ x y).2 - φ w * (T.evalNumerator φ x y).1,
        φ u * (if left then (T.evalNumerator φ x y).1 else (T.evalNumerator φ x y).2)) := by
  cases left <;> apply Prod.ext <;>
    simp only [evalNumerator, movingReverse, reverse, swap, GiantRows.swap,
      Bool.false_eq_true, ite_false, if_false, ite_true, if_true, map_mul, map_sub] <;> ring

theorem movingPolynomialAncestors_append_eval {σ R : Type*} [CommRing R]
    (φ : MvPolynomial σ ℤ →+* R) (a b : List (PolynomialReversal σ)) (x y : R) :
    (movingPolynomialAncestors (a ++ b)).evalNumerator φ x y =
      (movingPolynomialAncestors a).evalNumerator φ
        ((movingPolynomialAncestors b).evalNumerator φ x y).1
        ((movingPolynomialAncestors b).evalNumerator φ x y).2 := by
  induction a with
  | nil => simp [movingPolynomialAncestors, PolynomialGiantRows.evalNumerator,
      PolynomialGiantRows.identity, GiantRows.identity]
  | cons s a ih =>
    simp only [List.cons_append, movingPolynomialAncestors,
      PolynomialGiantRows.evalNumerator_movingReverse, ih]

theorem PolynomialGiantRows.evalNumerator_smul {σ R : Type*} [CommRing R]
    (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* R) (c x y : R) :
    T.evalNumerator φ (c * x) (c * y) =
      (c * (T.evalNumerator φ x y).1, c * (T.evalNumerator φ x y).2) := by
  apply Prod.ext <;> simp only [evalNumerator] <;> ring

theorem movingSlotLine_eval {σ R : Type*} [CommRing R]
    (φ : MvPolynomial σ ℤ →+* R) (path : List (MovingSlotReversal σ))
    (s : MovingSlotReversal σ) (x y : R) :
    φ (movingSlotLine path s).a * x + φ (movingSlotLine path s).b * y =
      φ s.polynomial.v * ((movingPolynomialAncestors
        (path.map MovingSlotReversal.polynomial)).evalNumerator φ x y).2 -
      φ s.polynomial.w * ((movingPolynomialAncestors
        (path.map MovingSlotReversal.polynomial)).evalNumerator φ x y).1 := by
  simp only [movingSlotLine, movingHistoryLine, PolynomialGiantRows.numeratorLine,
    PolynomialGiantRows.evalNumerator, map_mul, map_sub]
  ring

/-- A root division multiplies every descendant cleared line by its root
denominator. No integrality of the descendant path is needed. -/
theorem movingSlotLine_append_singleton {σ R : Type*} [CommRing R]
    (φ : MvPolynomial σ ℤ →+* R) (path : List (MovingSlotReversal σ))
    (current root : MovingSlotReversal σ) (x y p : R)
    (hroot : φ root.polynomial.v * y - φ root.polynomial.w * x = φ root.polynomial.u * p) :
    φ (movingSlotLine (path ++ [root]) current).a * x +
        φ (movingSlotLine (path ++ [root]) current).b * y =
      φ root.polynomial.u * (φ (movingSlotLine path current).a * p +
        φ (movingSlotLine path current).b * (if root.left then x else y)) := by
  rw [movingSlotLine_eval, movingSlotLine_eval, List.map_append,
    movingPolynomialAncestors_append_eval]
  have he : (movingPolynomialAncestors ([root].map MovingSlotReversal.polynomial)).evalNumerator φ x y =
      (φ root.polynomial.u * p, φ root.polynomial.u * (if root.left then x else y)) := by
    rw [List.map_cons, List.map_nil, movingPolynomialAncestors,
      PolynomialGiantRows.evalNumerator_movingReverse]
    simp only [MovingSlotReversal.polynomial] at hroot
    simp only [movingPolynomialAncestors, PolynomialGiantRows.evalNumerator,
      PolynomialGiantRows.identity, GiantRows.identity, map_one, map_zero,
      one_mul, zero_mul, add_zero, zero_add, MovingSlotReversal.polynomial, hroot]
  rw [he, PolynomialGiantRows.evalNumerator_smul]
  simp only
  ring

theorem movingSlotLine_append_singleton_zero_iff {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ))
    (current root : MovingSlotReversal σ) (x y p : ℤ)
    (hroot : root.signedNumerator value x y =
      root.rootFrequency * (MovingSlotReversal.naturalProduct value root.compensationSlots : ℤ) * p)
    (hu : MovingSlotReversal.naturalReduction q value root.polynomial.u ≠ 0) :
    let φ := MovingSlotReversal.naturalReduction q value
    φ (movingSlotLine (path ++ [root]) current).a * (x : ZMod q) +
        φ (movingSlotLine (path ++ [root]) current).b * (y : ZMod q) = 0 ↔
      φ (movingSlotLine path current).a * (p : ZMod q) +
        φ (movingSlotLine path current).b * ((if root.left then x else y : ℤ) : ZMod q) = 0 := by
  have hc := congrArg (fun z : ℤ => (z : ZMod q)) hroot
  simp only [MovingSlotReversal.signedNumerator, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast] at hc
  have hh : MovingSlotReversal.naturalReduction q value root.polynomial.v * (y : ZMod q) -
      MovingSlotReversal.naturalReduction q value root.polynomial.w * (x : ZMod q) =
      MovingSlotReversal.naturalReduction q value root.polynomial.u * (p : ZMod q) := by
    simp only [MovingSlotReversal.naturalReduction, MovingSlotReversal.polynomial,
      MovingSlotReversal.coefficient_nat_eval]
    linear_combination hc
  have he := movingSlotLine_append_singleton (MovingSlotReversal.naturalReduction q value)
    path current root (x : ZMod q) (y : ZMod q) (p : ZMod q) hh
  dsimp only
  rw [he, mul_eq_zero, or_iff_right hu]
  cases root.left <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeLineGate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The internal-prime gate on the original top giant pair -/

namespace Ostmann
open scoped Classical

theorem movingPrimeLineSupport_root {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n) (x y : ℤ)
    (h : movingPrimeLineSupport value (.node s CL CR U left right) x y) :
    ∀ i ∈ U, (value i : ℤ) ∣
      (MovingSlotData.step s CL CR U left right false).signedNumerator value x y := by
  intro i hi
  have he := h ⟨n + 1, MovingSlotData.step s CL CR U left right false, []⟩
    List.mem_cons_self i hi
  have hh : ((MovingSlotData.step s CL CR U left right false).signedNumerator value x y :
      ZMod (value i)) = 0 := by
    dsimp only at he
    rw [movingSlotLine_eval] at he
    simpa only [MovingSlotReversal.naturalReduction, MovingSlotReversal.signedNumerator,
      MovingSlotReversal.polynomial, MovingSlotReversal.coefficient_nat_eval,
      PolynomialGiantRows.evalNumerator, movingPolynomialAncestors, List.map_nil,
      PolynomialGiantRows.identity, GiantRows.identity, map_one, map_zero, one_mul,
      zero_mul, mul_zero, mul_one, add_zero, zero_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      mul_assoc, mul_comm, mul_left_comm] using he
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh

/-- Decomposition of the top-coordinate line gate after just the current
integer relation is known; descendant integrality is not an assumption. -/
theorem movingPrimeLineSupport_node {σ : Type*} (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n) (x y p : ℤ)
    (hrel : (MovingSlotData.step s CL CR U left right false).signedNumerator value x y =
      s * (MovingSlotReversal.naturalProduct value U : ℤ) * p)
    (hUL : ∀ o ∈ left.occurrences, ∀ i ∈ o.current.compensationSlots,
      MovingSlotReversal.naturalReduction (value i) value
        (MovingSlotData.step s CL CR U left right true).polynomial.u ≠ 0)
    (hUR : ∀ o ∈ right.occurrences, ∀ i ∈ o.current.compensationSlots,
      MovingSlotReversal.naturalReduction (value i) value
        (MovingSlotData.step s CL CR U left right false).polynomial.u ≠ 0) :
    movingPrimeLineSupport value (.node s CL CR U left right) x y ↔
      (∀ i ∈ U, (value i : ℤ) ∣
        (MovingSlotData.step s CL CR U left right false).signedNumerator value x y) ∧
      movingPrimeLineSupport value left p x ∧ movingPrimeLineSupport value right p y := by
  let step := MovingSlotData.step s CL CR U left right
  have hleft (o : MovingSlotOccurrence σ) (ho : o ∈ left.occurrences)
      (i : σ) (hi : i ∈ o.current.compensationSlots) :
      let φ := MovingSlotReversal.naturalReduction (value i) value
      φ (movingSlotLine (o.path ++ [step true]) o.current).a * (x : ZMod (value i)) +
          φ (movingSlotLine (o.path ++ [step true]) o.current).b * (y : ZMod (value i)) = 0 ↔
        φ (movingSlotLine o.path o.current).a * (p : ZMod (value i)) +
          φ (movingSlotLine o.path o.current).b * (x : ZMod (value i)) = 0 := by
    let : Fact (value i).Prime := ⟨hprime i⟩
    exact movingSlotLine_append_singleton_zero_iff value o.path o.current (step true)
      x y p hrel (hUL o ho i hi)
  have hright (o : MovingSlotOccurrence σ) (ho : o ∈ right.occurrences)
      (i : σ) (hi : i ∈ o.current.compensationSlots) :
      let φ := MovingSlotReversal.naturalReduction (value i) value
      φ (movingSlotLine (o.path ++ [step false]) o.current).a * (x : ZMod (value i)) +
          φ (movingSlotLine (o.path ++ [step false]) o.current).b * (y : ZMod (value i)) = 0 ↔
        φ (movingSlotLine o.path o.current).a * (p : ZMod (value i)) +
          φ (movingSlotLine o.path o.current).b * (y : ZMod (value i)) = 0 := by
    let : Fact (value i).Prime := ⟨hprime i⟩
    exact movingSlotLine_append_singleton_zero_iff value o.path o.current (step false)
      x y p hrel (hUR o ho i hi)
  constructor
  · intro h
    refine ⟨movingPrimeLineSupport_root value s CL CR U left right x y h, ?_, ?_⟩
    · intro o ho i hi
      apply (hleft o ho i hi).mp
      exact h (o.extend (step true)) (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩))) i hi
    · intro o ho i hi
      apply (hright o ho i hi).mp
      exact h (o.extend (step false)) (List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩))) i hi
  · rintro ⟨hroot, hL, hR⟩ o ho i hi
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (value i)).mpr (hroot i hi)
      dsimp only
      rw [movingSlotLine_eval]
      simpa only [MovingSlotReversal.naturalReduction, MovingSlotReversal.signedNumerator,
        MovingSlotReversal.polynomial, MovingSlotReversal.coefficient_nat_eval,
        PolynomialGiantRows.evalNumerator, movingPolynomialAncestors, List.map_nil,
        PolynomialGiantRows.identity, GiantRows.identity, map_one, map_zero, one_mul,
        zero_mul, mul_zero, mul_one, add_zero, zero_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
        mul_assoc, mul_comm, mul_left_comm] using hz
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        exact (hleft o' ho' i hi).mpr (hL o' ho' i hi)
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        exact (hright o' ho' i hi).mpr (hR o' ho' i hi)

theorem MovingSlotData.compensation_ancestor_unit {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (hf : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (o : MovingSlotOccurrence σ) (ho : o ∈ T.occurrences)
    (i : σ) (hi : i ∈ o.current.compensationSlots) :
    ∀ root ∈ o.path,
      MovingSlotReversal.naturalReduction (value i) value root.polynomial.u ≠ 0 := by
  have h := T.occurrence_units_of_prime_types tier value hprime hdisjoint hlevels o ho i
    (T.occurrence_compensation_level tier hlevels o ho i hi) (hf i)
  exact fun root hr => (h.1 root hr).2.2

theorem movingPrimeLineSupport_node_of_levels {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n)
    (hlevels : (MovingSlotData.node s CL CR U left right).Levels tier)
    (hf : ∀ i, (MovingSlotData.node s CL CR U left right).Frequencies
      (fun f => (f : ZMod (value i)) ≠ 0)) (x y p : ℤ)
    (hrel : (MovingSlotData.step s CL CR U left right false).signedNumerator value x y =
      s * (MovingSlotReversal.naturalProduct value U : ℤ) * p) :
    movingPrimeLineSupport value (.node s CL CR U left right) x y ↔
      (∀ i ∈ U, (value i : ℤ) ∣
        (MovingSlotData.step s CL CR U left right false).signedNumerator value x y) ∧
      movingPrimeLineSupport value left p x ∧ movingPrimeLineSupport value right p y := by
  apply movingPrimeLineSupport_node value hprime s CL CR U left right x y p hrel
  · intro o ho i hi
    exact (MovingSlotData.node s CL CR U left right).compensation_ancestor_unit
      tier value hprime hdisjoint hlevels hf (o.extend (MovingSlotData.step s CL CR U left right true))
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩)))
      i hi _ (by simp [MovingSlotOccurrence.extend])
  · intro o ho i hi
    exact (MovingSlotData.node s CL CR U left right).compensation_ancestor_unit
      tier value hprime hdisjoint hlevels hf (o.extend (MovingSlotData.step s CL CR U left right false))
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩)))
      i hi _ (by simp [MovingSlotOccurrence.extend])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingIntegralFrequencySplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact frequency and internal-prime splitting before real restrictions

All divisions here are integer divisions. Positivity is deliberately left to
the existing real gate. The equivalence recovers integer divisibility from
the two disjoint residue blocks, including at every descendant node.
-/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.frequencyPivot_signed_modEq {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (R : ℤ) (k : ℕ)
    (hs : s.rootFrequency ≠ 0)
    (hu : IsCoprime (naturalProduct value s.compensationSlots : ℤ) R)
    (x y : ℤ) (hI : s.SignedIntegralAt value x y) :
    s.frequencyPivot value R k x y ≡ s.signedPivot value x y [ZMOD R ^ k] := by
  unfold frequencyPivot
  rw [show s.signedNumerator value x y = s.rootFrequency *
      ((naturalProduct value s.compensationSlots : ℤ) * s.signedPivot value x y) by
    simpa only [SignedIntegralAt, mul_assoc] using hI]
  rw [Int.mul_ediv_cancel_left _ hs]
  simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using
    (coprime_bezout_inverse_modEq _ R hu k).mul_right (s.signedPivot value x y)

theorem pairwise_coprime_list_prod_int_dvd_iff (U : List ℕ)
    (hU : U.Pairwise Nat.Coprime) (N : ℤ) :
    (U.prod : ℤ) ∣ N ↔ ∀ b ∈ U, (b : ℤ) ∣ N := by
  simp only [Int.natCast_dvd, pairwise_coprime_list_prod_dvd_iff U hU]

theorem MovingSlotReversal.signedIntegral_of_prime_lines {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (R : ℤ)
    (hsR : s.rootFrequency ∣ R)
    (hu : IsCoprime (naturalProduct value s.compensationSlots : ℤ) R)
    (hp : (s.compensationSlots.map value).Pairwise Nat.Coprime) (x y : ℤ)
    (hs : s.rootFrequency ∣ s.signedNumerator value x y)
    (hlines : ∀ i ∈ s.compensationSlots, (value i : ℤ) ∣ s.signedNumerator value x y) :
    s.SignedIntegralAt value x y := by
  have hU : (naturalProduct value s.compensationSlots : ℤ) ∣ s.signedNumerator value x y := by
    apply (pairwise_coprime_list_prod_int_dvd_iff _ hp _).mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hlines i hi
  have hc : IsCoprime s.rootFrequency (naturalProduct value s.compensationSlots : ℤ) :=
    (hu.of_isCoprime_of_dvd_right hsR).symm
  have hd := hc.mul_dvd hs hU
  exact (Int.mul_ediv_cancel' hd).symm

/-- The frequency block and the simultaneous prime lines give precisely
the original signed integer recursion with its subtree-frequency unit tests.
This is an equivalence on every top pair, before the real support is imposed. -/
theorem moving_frequency_internal_split {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j) (R : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) R)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (hf : T.Frequencies (· ≠ 0))
    (hfmod : ∀ i, T.Frequencies (fun f => (f : ZMod (value i)) ≠ 0))
    (hR : T.frequencyProduct ∣ R) (hdistinct : T.CompensationDistinct value) (x y : ℤ) :
    movingFrequencyGate value R T x y ∧ movingPrimeLineSupport value T x y ↔
      T.SignedIntegral value x y ∧ movingSignedFrequencyUnits value T x y := by
  induction T generalizing x y with
  | leaf s C =>
    simp only [movingFrequencyGate, MovingSlotData.SignedIntegral, movingSignedFrequencyUnits,
      movingPrimeLineSupport, MovingSlotData.occurrences, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, true_and]
  | @node n s CL CR U left right ihL ihR =>
    let step := MovingSlotData.step s CL CR U left right false
    let p := step.signedPivot value x y
    let r := step.frequencyPivot value R (n + 1) x y
    have hd := MovingSlotData.frequencyProduct_node_dvd s CL CR U left right R hR
    have hU : IsCoprime (MovingSlotReversal.naturalProduct value U : ℤ) R :=
      movingNaturalProduct_coprime value U R (fun i _ => hsmall i)
    have hstep (hI : step.SignedIntegralAt value x y) :
        movingFrequencyGate value R left r x ↔ movingFrequencyGate value R left p x := by
      exact movingFrequencyGate_modEq value R left hf.2.1 hd.2.1 r x p x
        (step.frequencyPivot_signed_modEq value R (n + 1) hf.1 hU x y hI) (Int.ModEq.refl _)
    have hstepR (hI : step.SignedIntegralAt value x y) :
        movingFrequencyGate value R right r y ↔ movingFrequencyGate value R right p y := by
      exact movingFrequencyGate_modEq value R right hf.2.2 hd.2.2 r y p y
        (step.frequencyPivot_signed_modEq value R (n + 1) hf.1 hU x y hI) (Int.ModEq.refl _)
    have hline (hI : step.SignedIntegralAt value x y) :=
      movingPrimeLineSupport_node_of_levels tier value hprime hdisjoint s CL CR U left right
        hlevels hfmod x y p hI
    have hl := ihL hlevels.2.2.2.1 hf.2.1 (fun i => (hfmod i).2.1) hd.2.1 hdistinct.2.1 p x
    have hr := ihR hlevels.2.2.2.2 hf.2.2 (fun i => (hfmod i).2.2) hd.2.2 hdistinct.2.2 p y
    constructor
    · rintro ⟨hfreq, hlines⟩
      have hroot := movingPrimeLineSupport_root value s CL CR U left right x y hlines
      have hI : step.SignedIntegralAt value x y :=
        step.signedIntegral_of_prime_lines value R hd.1 hU hdistinct.1 x y hfreq.2.1 hroot
      have hlines' := (hline hI).mp hlines
      have hL := hl.mp ⟨(hstep hI).mp hfreq.2.2.1, hlines'.2.1⟩
      have hR := hr.mp ⟨(hstepR hI).mp hfreq.2.2.2, hlines'.2.2⟩
      exact ⟨⟨hI, hL.1, hR.1⟩, hfreq.1, hL.2, hR.2⟩
    · rintro ⟨⟨hI, hIL, hIR⟩, hunit, hUL, hUR⟩
      have hL := hl.mpr ⟨hIL, hUL⟩
      have hR := hr.mpr ⟨hIR, hUR⟩
      have hdiv : s ∣ step.signedNumerator value x y :=
        ⟨_, by simpa only [MovingSlotReversal.SignedIntegralAt, step,
          MovingSlotData.step, mul_assoc] using hI⟩
      have hroot : ∀ i ∈ U, (value i : ℤ) ∣ step.signedNumerator value x y := by
        intro i hi
        have hp : value i ∣ MovingSlotReversal.naturalProduct value U :=
          List.dvd_prod (List.mem_map.mpr ⟨i, hi, rfl⟩)
        rw [hI]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hp) _) _
      exact ⟨⟨hunit, hdiv, (hstep hI).mpr hL.1, (hstepR hI).mpr hR.1⟩,
        (hline hI).mpr ⟨hroot, hL.2, hR.2⟩⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedFormulas
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original rational node formulas and the signed integer recursion -/

namespace Ostmann
open scoped Classical

theorem rational_int_div_integral_iff (N D : ℤ) (hD : D ≠ 0) :
    (∃ z : ℤ, (N : ℚ) / D = z) ↔ D ∣ N := by
  constructor
  · rintro ⟨z, hz⟩
    have he := (div_eq_iff (Int.cast_ne_zero.mpr hD)).mp hz
    have hi : N = z * D := by exact_mod_cast he
    exact ⟨z, by simpa only [mul_comm] using hi⟩
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [Int.cast_mul]
    exact mul_div_cancel_left₀ (z : ℚ) (Int.cast_ne_zero.mpr hD)

theorem MovingSlotReversal.giantFormula_signed_value {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (hs : step.rootFrequency ≠ 0)
    (hu : naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ)) :
    (step.giantFormula value hs hu L R).value (fun b => (a b : ℚ)) =
      (step.signedNumerator value x y : ℚ) /
        (step.rootFrequency * (naturalProduct value step.compensationSlots : ℤ)) := by
  simp only [giantFormula, HistoryFormula.value_solve, HistoryFormula.value_product,
    HistoryFormula.value_external, hL, hR, signedNumerator, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast]

theorem MovingSlotReversal.giantFormula_signed_integral_iff {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (hs : step.rootFrequency ≠ 0)
    (hu : naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ)) :
    (step.giantFormula value hs hu L R).IntegralAt a ↔ step.SignedIntegralAt value x y := by
  change (∃ z : ℤ, (step.giantFormula value hs hu L R).value _ = (z : ℚ)) ↔ _
  rw [step.giantFormula_signed_value value hs hu L R a x y hL hR]
  simp only [← Int.cast_mul]
  rw [rational_int_div_integral_iff _ _ (mul_ne_zero hs (Int.natCast_ne_zero.mpr hu))]
  change _ ∣ _ ↔ _ = _
  constructor
  · intro hd
    exact (Int.mul_ediv_cancel' hd).symm
  · intro h
    exact ⟨step.signedPivot value x y, h⟩

theorem MovingSlotReversal.giantFormula_of_signed_integral {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (hs : step.rootFrequency ≠ 0)
    (hu : naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ))
    (hI : step.SignedIntegralAt value x y) :
    (step.giantFormula value hs hu L R).value (fun b => (a b : ℚ)) =
      (step.signedPivot value x y : ℚ) := by
  rw [step.giantFormula_signed_value value hs hu L R a x y hL hR, hI]
  push_cast
  field_simp

/-- The integrality entries of the original formula list impose exactly
the signed divisions. They do not need any real or positivity hypothesis. -/
theorem MovingSlotData.formulaNodes_signed_integral_iff {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ)) :
    (∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R, f.newGiant.IntegralAt a) ↔
      T.SignedIntegral value x y := by
  induction T generalizing L R x y with
  | leaf => simp [formulaNodes, SignedIntegral]
  | @node n s CL CR U left right ihL ihR =>
    let step := MovingSlotData.step s CL CR U left right false
    have hU := MovingSlotReversal.naturalProduct_ne_zero value hvalue U
    let G := step.giantFormula value hf.1 hU L R
    have hroot := step.giantFormula_signed_integral_iff value hf.1 hU L R a x y hL hR
    simp only [formulaNodes, List.forall_mem_cons, List.forall_mem_append]
    change (G.IntegralAt a ∧ (∀ f ∈ left.formulaNodes value hvalue childBound pivotBound hf.2.1 G L,
      f.newGiant.IntegralAt a) ∧ (∀ f ∈ right.formulaNodes value hvalue childBound pivotBound hf.2.2 G R,
      f.newGiant.IntegralAt a)) ↔ _
    constructor
    · rintro ⟨hG, hl, hr⟩
      have hI := hroot.mp hG
      have hval := step.giantFormula_of_signed_integral value hf.1 hU L R a x y hL hR hI
      exact ⟨hI, (ihL hf.2.1 G L _ _ hval hL).mp hl, (ihR hf.2.2 G R _ _ hval hR).mp hr⟩
    · rintro ⟨hI, hl, hr⟩
      have hval := step.giantFormula_of_signed_integral value hf.1 hU L R a x y hL hR hI
      exact ⟨hroot.mpr hI, (ihL hf.2.1 G L _ _ hval hL).mpr hl, (ihR hf.2.2 G R _ _ hval hR).mpr hr⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyFormulaGate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original formula gate in frequency and internal-prime coordinates -/

namespace Ostmann
open scoped Classical

theorem movingNodeGuard_signed_values {σ : Type*}
    (value : σ → ℕ) (step : MovingSlotReversal σ) (hs : step.rootFrequency ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ)) :
    let g := movingNodeGuard (MovingSlotReversal.naturalProduct value step.leftSlots)
      (MovingSlotReversal.naturalProduct value step.rightSlots)
      step.rootFrequency step.leftFrequency step.rightFrequency hs childBound pivotBound L R
    g.pivot.value (fun b => (a b : ℚ)) =
        (step.signedNumerator value x y : ℚ) / step.rootFrequency ∧
      g.rightProduct.value (fun b => (a b : ℚ)) =
        ((y * MovingSlotReversal.naturalProduct value step.rightSlots : ℤ) : ℚ) := by
  dsimp only
  simp only [movingNodeGuard, wordTransferGuard, wordTransferStep, HistoryPivotStep.formula,
    movingNodeWord, HistoryFormula.value_bind, HistoryFormula.value_solve,
    HistoryFormula.value_listProduct, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, HistoryFormula.value_prime, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
    HistoryFormula.value_product, HistoryFormula.value_external, hL, hR,
    MovingSlotReversal.signedNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    mul_one, and_self]

theorem movingNodeGuard_residue_of_signedIntegral {σ : Type*}
    (value : σ → ℕ) (step : MovingSlotReversal σ) (hs : step.rootFrequency ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ))
    (hI : step.SignedIntegralAt value x y)
    (hroot : IsCoprime step.rootFrequency
      (y * MovingSlotReversal.naturalProduct value step.rightSlots : ℤ))
    (hpivot : IsCoprime step.rightFrequency
      ((MovingSlotReversal.naturalProduct value step.compensationSlots : ℤ) * step.signedPivot value x y)) :
    (movingNodeGuard (MovingSlotReversal.naturalProduct value step.leftSlots)
      (MovingSlotReversal.naturalProduct value step.rightSlots)
      step.rootFrequency step.leftFrequency step.rightFrequency hs childBound pivotBound L R).residueAt a := by
  let g := movingNodeGuard (MovingSlotReversal.naturalProduct value step.leftSlots)
    (MovingSlotReversal.naturalProduct value step.rightSlots)
    step.rootFrequency step.leftFrequency step.rightFrequency hs childBound pivotBound L R
  have hv := movingNodeGuard_signed_values value step hs childBound pivotBound L R a x y hL hR
  have hP : g.pivot.value (fun b => (a b : ℚ)) =
      (((MovingSlotReversal.naturalProduct value step.compensationSlots : ℤ) * step.signedPivot value x y : ℤ) : ℚ) := by
    rw [hv.1, hI]
    push_cast
    field_simp
  change g.residueAt a
  unfold WordTransferGuard.residueAt
  rw [g.pivot.smallDivisionTest_of_value a _ hP,
    g.rightProduct.smallDivisionTest_of_value a _ hv.2]
  constructor
  · change IsUnit (((MovingSlotReversal.naturalProduct value step.compensationSlots : ℤ) *
      step.signedPivot value x y : ℤ) : ZMod step.rightFrequency.natAbs)
    rwa [ZMod.coe_int_isUnit_iff_isCoprime, Int.natCast_natAbs, IsCoprime.abs_left_iff]
  · change IsUnit ((y * (MovingSlotReversal.naturalProduct value step.rightSlots : ℤ) : ℤ) :
      ZMod step.rootFrequency.natAbs)
    rwa [ZMod.coe_int_isUnit_iff_isCoprime, Int.natCast_natAbs, IsCoprime.abs_left_iff]

theorem movingSignedFrequencyUnits_local {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ)
    (h : movingSignedFrequencyUnits value T x y) : movingFrequencyLocalUnits T x y := by
  cases T with
  | leaf => exact h
  | node => exact h.1

theorem MovingSlotData.formulaNodes_residue_of_signedIntegral {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun f => IsCoprime f (value i : ℤ)))
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ))
    (hI : T.SignedIntegral value x y) (hunit : movingSignedFrequencyUnits value T x y) :
    ∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R, f.residueTests a := by
  induction T generalizing L R x y with
  | leaf => simp [formulaNodes]
  | @node n s CL CR U left right ihL ihR =>
    let step := MovingSlotData.step s CL CR U left right false
    have hU := MovingSlotReversal.naturalProduct_ne_zero value hvalue U
    let G := step.giantFormula value hf.1 hU L R
    have hG := step.giantFormula_of_signed_integral value hf.1 hU L R a x y hL hR hI.1
    have hroot : IsCoprime s (y * (MovingSlotReversal.naturalProduct value CR : ℤ)) := by
      apply IsCoprime.mul_right
      · exact ((MovingSlotData.node s CL CR U left right).frequencies_isCoprime y |>.mpr hunit.1.2).root.symm
      · exact (movingNaturalProduct_coprime value CR s
          (fun i _ => (hsmall i).root.symm)).symm
    have hpivot : IsCoprime right.frequency
        ((MovingSlotReversal.naturalProduct value U : ℤ) * step.signedPivot value x y) := by
      apply IsCoprime.mul_right
      · exact (movingNaturalProduct_coprime value U right.frequency
          (fun i _ => (hsmall i).2.2.root.symm)).symm
      · exact ((right.frequencies_isCoprime (step.signedPivot value x y)).mpr
          (movingSignedFrequencyUnits_local value right _ _ hunit.2.2).1).root.symm
    have hguard := movingNodeGuard_residue_of_signedIntegral value step hf.1
      (childBound (n + 1)) (pivotBound (n + 1)) L R a x y hL hR hI.1 hroot hpivot
    have hl := ihL hf.2.1 (fun i => (hsmall i).2.1) G L _ _ hG hL hI.2.1 hunit.2.1
    have hr := ihR hf.2.2 (fun i => (hsmall i).2.2) G R _ _ hG hR hI.2.2 hunit.2.2
    intro f hmem
    rcases List.mem_cons.mp hmem with hmem | hmem
    · subst f
      exact (MovingFormulaNode.residueTests_iff _ a).mpr
        ⟨hguard, step.giantFormula_signed_integral_iff value hf.1 hU L R a x y hL hR |>.mpr hI.1⟩
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact hl f hmem
      · exact hr f hmem

theorem moving_formula_residue_frequency_internal_iff {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j) (R₀ : ℤ)
    (hsmallR : ∀ i, IsCoprime (value i : ℤ) R₀)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun f => IsCoprime f (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun f => (f : ZMod (value i)) ≠ 0))
    (hR₀ : T.frequencyProduct ∣ R₀) (hdistinct : T.CompensationDistinct value)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ)) :
    let nodes := T.formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound hf L R
    movingResidueGate nodes a ∧ movingSignedFrequencyUnits value T x y ↔
      (∀ f ∈ nodes, f.guard.frequencyBounds) ∧
        movingFrequencyGate value R₀ T x y ∧ movingPrimeLineSupport value T x y := by
  let hvalue := fun i => (hprime i).ne_zero
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf L R
  have hint := T.formulaNodes_signed_integral_iff value hvalue childBound pivotBound hf L R a x y hL hR
  have hsplit := moving_frequency_internal_split tier value hprime hdisjoint R₀ hsmallR
    T hlevels hf hfmod hR₀ hdistinct x y
  change (movingResidueGate nodes a ∧ _) ↔ (∀ f ∈ nodes, _) ∧ _ ∧ _
  constructor
  · rintro ⟨hres, hunit⟩
    have hI : T.SignedIntegral value x y := hint.mp (fun f hf =>
      (f.residueTests_iff a).mp (hres f hf).1 |>.2)
    exact ⟨fun f hf => (hres f hf).2, hsplit.mpr ⟨hI, hunit⟩⟩
  · rintro ⟨hb, hg, hl⟩
    obtain ⟨hI, hunit⟩ := hsplit.mp ⟨hg, hl⟩
    have htests := T.formulaNodes_residue_of_signedIntegral value hvalue childBound pivotBound
      hf hsmall L R a x y hL hR hI hunit
    exact ⟨fun f hf => ⟨htests f hf, hb f hf⟩, hunit⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingModularSpectator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spectator evaluation without internal primes in the period

At a spectator prime the entire reversal denominator is a unit. The field
recursion therefore depends only on the two spectator residues, even though
the original recursion used integer division by compensation products.
-/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.modularDenominators_of_units {σ : Type*}
    (value : σ → ℕ) (q : ℕ) [Fact q.Prime] (hvalue : ∀ i, (value i : ZMod q) ≠ 0)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (fun s => (s : ZMod q) ≠ 0)) :
    T.ModularDenominators value q := by
  induction T with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    refine ⟨hf.1, ?_, ihL hf.2.1, ihR hf.2.2⟩
    have hp : (U.map fun i => (value i : ZMod q)).prod ≠ 0 := by
      apply List.prod_ne_zero
      intro hz
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hz
      exact hvalue i hi
    simpa only [MovingSlotReversal.naturalProduct, Nat.cast_list_prod,
      List.map_map, Function.comp_def] using hp

theorem MovingSlotReversal.modularPivot_of_signedIntegral {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (q : ℕ) [Fact q.Prime]
    (hs : (step.rootFrequency : ZMod q) ≠ 0)
    (hu : (MovingSlotReversal.naturalProduct value step.compensationSlots : ZMod q) ≠ 0)
    (x y : ℤ) (hI : step.SignedIntegralAt value x y) :
    step.modularPivot value q x y = (step.signedPivot value x y : ZMod q) := by
  have he := congrArg (fun z : ℤ => (z : ZMod q)) hI
  simp only [MovingSlotReversal.signedNumerator,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast] at he
  unfold modularPivot
  apply (div_eq_iff (mul_ne_zero hs hu)).mpr
  linear_combination he

theorem movingSignedSpectator_eq_modular {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (hden : T.ModularDenominators value q)
    (x y : ℤ) (hI : T.SignedIntegral value x y) :
    movingSignedSpectator value g D T x y = movingModularSpectator value q g D T x y := by
  induction T generalizing x y with
  | leaf => simp only [movingSignedSpectator, movingModularSpectator, Int.cast_mul, Int.cast_natCast]
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedSpectator, movingModularSpectator,
      (MovingSlotData.step s CL CR U left right false).modularPivot_of_signedIntegral
        value q hden.1 hden.2.1 x y hI.1]
    split_ifs
    · rfl
    · rw [ihL hden.2.2.1 _ _ hI.2.1, ihR hden.2.2.2 _ _ hI.2.2]

theorem movingModularSpectator_norm {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ z, ‖g z‖ ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q) :
    ‖movingModularSpectator value q g D T x y‖ ≤ B ^ (2 ^ n) := by
  induction T generalizing x y with
  | leaf => simpa only [movingModularSpectator, pow_zero, pow_one] using hg _
  | @node n s CL CR U left right ihL ihR =>
    rw [movingModularSpectator]
    split_ifs
    · simpa only [norm_zero] using pow_nonneg hB (2 ^ (n + 1))
    · rw [norm_mul, norm_star]
      calc
        _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
          mul_le_mul (ihL _ _) (ihR _ _) (norm_nonneg _) (pow_nonneg hB _)
        _ = B ^ (2 ^ (n + 1)) := by rw [← pow_add, pow_succ]; congr 1; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOutsideResidues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outside giant-unit tests in spectator coordinates -/

namespace Ostmann
open scoped Classical

theorem movingSignedAuxiliaryUnits_split {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) :
    movingSignedAuxiliaryUnits value outside T x y ↔
      movingSignedFrequencyUnits value T x y ∧ movingSignedOutsideUnits value outside.prod T x y := by
  induction T generalizing x y with
  | leaf =>
    simp only [movingSignedAuxiliaryUnits, movingSignedFrequencyUnits,
      movingSignedOutsideUnits, movingAuxiliaryLocalUnits, movingFrequencyLocalUnits]
    tauto
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedAuxiliaryUnits, movingSignedFrequencyUnits,
      movingSignedOutsideUnits, movingAuxiliaryLocalUnits, movingFrequencyLocalUnits, ihL, ihR]
    tauto

theorem movingModularGiantUnits_local {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q)
    (h : movingModularGiantUnits value q T x y) : x ≠ 0 ∧ y ≠ 0 := by
  cases T with
  | leaf => exact h
  | node => exact h.1

theorem movingSignedOutsideUnits_modular {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] {n : ℕ} (T : MovingSlotData σ n)
    (hden : T.ModularDenominators value q) (x y : ℤ) (hI : T.SignedIntegral value x y) :
    movingSignedOutsideUnits value q T x y ↔ movingModularGiantUnits value q T x y := by
  have hlocal (z : ℤ) : IsCoprime z (q : ℤ) ↔ (z : ZMod q) ≠ 0 := by
    rw [isCoprime_comm, ← ZMod.coe_int_isUnit_iff_isCoprime, isUnit_iff_ne_zero]
  induction T generalizing x y with
  | leaf => exact and_congr (hlocal x) (hlocal y)
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedOutsideUnits, movingModularGiantUnits,
      (MovingSlotData.step s CL CR U left right false).modularPivot_of_signedIntegral
        value q hden.1 hden.2.1 x y hI.1, hlocal,
      ihL hden.2.2.1 _ _ hI.2.1, ihR hden.2.2.2 _ _ hI.2.2]

/-- With the original zero convention, a nonzero spectator coefficient
already enforces every outside giant-unit test at that prime. -/
theorem movingModularSpectator_nonzero_units {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (hg0 : g 0 = 0)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q)
    (h : movingModularSpectator value q g D T x y ≠ 0) :
    movingModularGiantUnits value q T x y := by
  induction T generalizing x y with
  | leaf s C =>
    constructor
    · intro hx
      exact h (by simp [movingModularSpectator, hx, hg0])
    · intro hy
      exact h (by simp [movingModularSpectator, hy, hg0])
  | node s CL CR U left right ihL ihR =>
    let p := (MovingSlotData.step s CL CR U left right false).modularPivot value q x y
    have hp : p ≠ 0 := by
      intro hp
      exact h (by simp only [movingModularSpectator, p, hp, ite_true, if_true])
    have hm : movingModularSpectator value q g D left p x *
        star (movingModularSpectator value q g D right p y) ≠ 0 := by
      simpa only [movingModularSpectator, show
        (MovingSlotData.step s CL CR U left right false).modularPivot value q x y ≠ 0 from hp,
        ite_false, if_false] using h
    have hl := ihL p x (mul_ne_zero_iff.mp hm).1
    have hr := ihR p y (by
      intro hz
      exact (mul_ne_zero_iff.mp hm).2 (by rw [hz, star_zero]))
    exact ⟨⟨(movingModularGiantUnits_local value q left p x hl).2,
      (movingModularGiantUnits_local value q right p y hr).2⟩, hl, hr⟩

theorem movingSignedOutsideUnits_mul {σ : Type*} (value : σ → ℕ) (M N : ℤ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) :
    movingSignedOutsideUnits value (M * N) T x y ↔
      movingSignedOutsideUnits value M T x y ∧ movingSignedOutsideUnits value N T x y := by
  induction T generalizing x y with
  | leaf => simp only [movingSignedOutsideUnits, IsCoprime.mul_right_iff]; tauto
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedOutsideUnits, IsCoprime.mul_right_iff, ihL, ihR]
    tauto

theorem movingSignedOutsideUnits_one {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) : movingSignedOutsideUnits value 1 T x y := by
  induction T generalizing x y with
  | leaf => exact ⟨isCoprime_one_right, isCoprime_one_right⟩
  | node s CL CR U left right ihL ihR =>
    exact ⟨⟨isCoprime_one_right, isCoprime_one_right⟩, ihL _ _, ihR _ _⟩

theorem movingSignedOutsideUnits_list {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) :
    movingSignedOutsideUnits value (outside.prod : ℤ) T x y ↔
      ∀ q ∈ outside, movingSignedOutsideUnits value (q : ℤ) T x y := by
  induction outside with
  | nil => simp only [List.prod_nil, Nat.cast_one, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, iff_true]; exact movingSignedOutsideUnits_one value T x y
  | cons q outside ih =>
    simp only [List.prod_cons, Nat.cast_mul, movingSignedOutsideUnits_mul, ih,
      List.forall_mem_cons]

theorem movingModularSpectatorProduct_outside_units {σ I : Type*}
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (hg0 : ∀ i ∈ S, g i 0 = 0) (outside : List ℕ)
    (hcover : ∀ p ∈ outside, ∃ i ∈ S, q i = p)
    {n : ℕ} (T : MovingSlotData σ n) (hden : ∀ i ∈ S, T.ModularDenominators value (q i))
    (x y : ℤ) (hI : T.SignedIntegral value x y)
    (hz : (∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T x y) ≠ 0) :
    movingSignedOutsideUnits value (outside.prod : ℤ) T x y := by
  apply (movingSignedOutsideUnits_list value outside T x y).mpr
  intro p hp
  obtain ⟨i, hi, rfl⟩ := hcover p hp
  apply (movingSignedOutsideUnits_modular value (q i) T (hden i hi) x y hI).mpr
  apply movingModularSpectator_nonzero_units value (q i) (g i) (D i) (hg0 i hi) T x y
  exact (Finset.prod_ne_zero_iff.mp hz) i hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original remainder coefficient in separated arithmetic coordinates -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSpectatorResidue_eq_modularProduct {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hden : ∀ i ∈ S, T.ModularDenominators value (q i))
    (x y : ℤ) (hI : T.SignedIntegral value x y) :
    movingSpectatorResidue q value g D S T x y =
      ∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T x y := by
  apply Finset.prod_congr rfl
  intro i hi
  exact movingSignedSpectator_eq_modular value (q i) (g i) (D i) T (hden i hi) x y hI

/-- Exact identity for the literal original reduced residue coefficient.
Its frequency factor has a frequency-only period; the other factors use
only internal-prime squares and individual spectator primes. -/
theorem movingReducedResidueCoefficient_eq_separated {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (hcover : ∀ p ∈ outside, ∃ i ∈ S, q i = p)
    (hg0 : ∀ i ∈ S, g i 0 = 0)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun f => IsCoprime f (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun f => (f : ZMod (value i)) ≠ 0))
    (R₀ : ℤ) (hR₀ : T.frequencyProduct ∣ R₀)
    (hsmallR : ∀ i, IsCoprime (value i : ℤ) R₀) (hdistinct : T.CompensationDistinct value)
    (hden : ∀ i ∈ S, T.ModularDenominators value (q i)) (a b : ℕ) :
    let nodes := T.formulaNodes value (fun i => (hprime i).ne_zero)
      childBound pivotBound hf (.prime false) (.prime true)
    movingReducedResidueWeight value outside T a b
        (movingResidueCoefficient q value F E g D S T nodes a b) =
      movingSeparatedResidueCoefficient q value outside F E g D S T nodes R₀ a b := by
  let hvalue := fun i => (hprime i).ne_zero
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  let input := topGiantInput a b
  let z := ∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T (a : ℤ) (b : ℤ)
  have hL : (HistoryFormula.prime false).value (fun j => (input j : ℚ)) = (a : ℚ) := by
    simp [input, topGiantInput]
  have hR : (HistoryFormula.prime true).value (fun j => (input j : ℚ)) = (b : ℚ) := by
    simp [input, topGiantInput]
  have hbridge := moving_formula_residue_frequency_internal_iff tier value hprime hdisjoint
    R₀ hsmallR childBound pivotBound T hlevels hf hsmall hfmod hR₀ hdistinct
    (.prime false) (.prime true) input a b hL hR
  have hint := T.formulaNodes_signed_integral_iff value hvalue childBound pivotBound hf
    (.prime false) (.prime true) input a b hL hR
  have hspec (hI : T.SignedIntegral value a b) : movingSpectatorResidue q value g D S T a b = z :=
    movingSpectatorResidue_eq_modularProduct q value g D S T hden a b hI
  have hmask : movingReducedResidueWeight value outside T a b
        (movingResidueCoefficient q value F E g D S T nodes a b) =
      if movingReducedResidueSupport value outside T a b ∧ movingResidueGate nodes input then
        movingSpectatorResidue q value g D S T a b * movingDataWeight F E T else 0 := by
    change (if movingReducedResidueSupport value outside T a b then
      ((if movingResidueGate nodes input then 1 else 0) *
        movingSpectatorResidue q value g D S T a b) * movingDataWeight F E T else 0) = _
    by_cases ha : movingReducedResidueSupport value outside T a b <;>
      by_cases hb : movingResidueGate nodes input <;> simp [ha, hb]
  change movingReducedResidueWeight value outside T a b
      (movingResidueCoefficient q value F E g D S T nodes a b) = _
  rw [hmask]
  by_cases hold : movingReducedResidueSupport value outside T a b ∧ movingResidueGate nodes input
  · have haux := (movingSignedAuxiliaryUnits_split value outside T a b).mp hold.1.2.2
    have hs := hbridge.mp ⟨hold.2, haux.1⟩
    have hnew : movingSeparatedSupport value outside T nodes R₀ a b :=
      ⟨hold.1.1, hold.1.2.1, hs⟩
    have hI : T.SignedIntegral value a b := hint.mp (fun f hf =>
      (f.residueTests_iff input).mp (hold.2 f hf).1 |>.2)
    rw [ite_eq_left hold]
    change _ = if movingSeparatedSupport value outside T nodes R₀ a b then _ else 0
    rw [ite_eq_left hnew, hspec hI]
  · rw [ite_eq_right hold]
    unfold movingSeparatedResidueCoefficient
    by_cases hnew : movingSeparatedSupport value outside T nodes R₀ a b
    · rw [ite_eq_left hnew]
      have hs := (moving_frequency_internal_split tier value hprime hdisjoint R₀ hsmallR
        T hlevels hf hfmod hR₀ hdistinct a b).mp hnew.2.2.2
      have hres := (hbridge.mpr ⟨hnew.2.2.1, hnew.2.2.2⟩).1
      have hz : z = 0 := by
        by_contra hz
        have hout := movingModularSpectatorProduct_outside_units value q g D S hg0 outside hcover
          T hden a b hs.1 hz
        have haux := (movingSignedAuxiliaryUnits_split value outside T a b).mpr ⟨hs.2, hout⟩
        exact hold ⟨⟨hnew.1, hnew.2.1, haux⟩, hres⟩
      exact (show z * movingDataWeight F E T = 0 by rw [hz, zero_mul]).symm
    · rw [ite_eq_right hnew]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Periodicity after the arithmetic factors have been separated -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPrimeLineSupport_modEq {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y a b M : ℤ)
    (hprime : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i : ℤ) ∣ M)
    (hx : x ≡ a [ZMOD M]) (hy : y ≡ b [ZMOD M]) :
    movingPrimeLineSupport value T x y ↔ movingPrimeLineSupport value T a b := by
  apply forall₂_congr
  intro o ho
  apply forall₂_congr
  intro i hi
  have hL : (x : ZMod (value i)) = (a : ZMod (value i)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hx.of_dvd (by exact_mod_cast hprime o ho i hi))
  have hR : (y : ZMod (value i)) = (b : ZMod (value i)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hy.of_dvd (by exact_mod_cast hprime o ho i hi))
  dsimp only
  rw [hL, hR]

theorem movingSeparatedSupport_modEq {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode)
    (R : ℤ) (hf : T.Frequencies (· ≠ 0)) (hR : T.frequencyProduct ∣ R)
    (x y a b M : ℤ) (hfrequency : R ^ (n + 1) ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hx : x ≡ a [ZMOD M]) (hy : y ≡ b [ZMOD M]) :
    movingSeparatedSupport value outside T nodes R x y ↔
      movingSeparatedSupport value outside T nodes R a b := by
  have hp : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i : ℤ) ∣ M := by
    intro o ho i hi
    exact (dvd_pow_self (value i : ℤ) (by decide : 2 ≠ 0)).trans (hsquare o ho i hi)
  unfold movingSeparatedSupport
  rw [movingSquareLineSupport_modEq value T x y a b M hsquare hx hy,
    movingFrequencyGate_modEq value R T hf hR x y a b (hx.of_dvd hfrequency) (hy.of_dvd hfrequency),
    movingPrimeLineSupport_modEq value T x y a b M hp hx hy]

theorem movingSeparatedResidueCoefficient_modEq {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode)
    (R : ℤ) (hf : T.Frequencies (· ≠ 0)) (hR : T.frequencyProduct ∣ R)
    (x y a b M : ℤ) (hfrequency : R ^ (n + 1) ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hspectator : ∀ i ∈ S, (q i : ℤ) ∣ M)
    (hx : x ≡ a [ZMOD M]) (hy : y ≡ b [ZMOD M]) :
    movingSeparatedResidueCoefficient q value outside F E g D S T nodes R x y =
      movingSeparatedResidueCoefficient q value outside F E g D S T nodes R a b := by
  have hs := movingSeparatedSupport_modEq value outside T nodes R hf hR x y a b M hfrequency hsquare hx hy
  have hprod : (∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T x y) =
      ∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T a b := by
    apply Finset.prod_congr rfl
    intro i hi
    have hL : (x : ZMod (q i)) = (a : ZMod (q i)) :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hx.of_dvd (by exact_mod_cast hspectator i hi))
    have hR : (y : ZMod (q i)) = (b : ZMod (q i)) :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hy.of_dvd (by exact_mod_cast hspectator i hi))
    rw [hL, hR]
  simp only [movingSeparatedResidueCoefficient, hs, hprod]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal original weight at the separated modulus -/

namespace Ostmann
open scoped Classical SchwartzMap

theorem MovingSlotData.CompensationPrimeData.distinct {σ : Type*}
    {value : σ → ℕ} {n : ℕ} {T : MovingSlotData σ n}
    (h : T.CompensationPrimeData value) : T.CompensationDistinct value := by
  induction T with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    exact ⟨h.2.1, ihL h.2.2.2.1, ihR h.2.2.2.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated two-history coefficient -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingSeparatedPairResidueCoefficient_modEq {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (hf : ∀ side, (T side).Frequencies (· ≠ 0))
    (hR : ∀ side, (T side).frequencyProduct ∣ R)
    (a b c d : ℕ) (M : ℤ) (hfrequency : R ^ (n + 1) ∣ M)
    (hsquare : ∀ side, ∀ o ∈ (T side).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hspectator : ∀ i ∈ S, (q i : ℤ) ∣ M)
    (hL : (a : ℤ) ≡ (c : ℤ) [ZMOD M]) (hRight : (b : ℤ) ≡ (d : ℤ) [ZMOD M]) :
    movingSeparatedPairResidueCoefficient q value outside F E g Dq S T nodes R a b =
      movingSeparatedPairResidueCoefficient q value outside F E g Dq S T nodes R c d := by
  have he (side : Bool) := movingSeparatedResidueCoefficient_modEq q value outside
    (F side) (E side) g (Dq side) S (T side) (nodes side) R (hf side) (hR side)
    a b c d M hfrequency (hsquare side) hspectator hL hRight
  unfold movingSeparatedPairResidueCoefficient
  rw [he false, he true]

theorem movingReducedPairResidueCoefficient_eq_separated {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (hcover : ∀ p ∈ outside, ∃ i ∈ S, q i = p) (hg0 : ∀ i ∈ S, g i 0 = 0)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (hf : ∀ side, (T side).Frequencies (· ≠ 0))
    (hsmall : ∀ side i, (T side).Frequencies (fun f => IsCoprime f (value i : ℤ)))
    (hfmod : ∀ side i, (T side).Frequencies (fun f => (f : ZMod (value i)) ≠ 0))
    (R : ℤ) (hR : ∀ side, (T side).frequencyProduct ∣ R)
    (hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
    (hdistinct : ∀ side, (T side).CompensationDistinct value)
    (hden : ∀ side i, i ∈ S → (T side).ModularDenominators value (q i)) (a b : ℕ) :
    let nodes := fun side => (T side).formulaNodes value (fun i => (hprime i).ne_zero)
      childBound pivotBound (hf side) (.prime false) (.prime true)
    movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes a b =
      movingSeparatedPairResidueCoefficient q value outside F E g Dq S T nodes R a b := by
  have he (side : Bool) := movingReducedResidueCoefficient_eq_separated q tier value hprime hdisjoint
    outside childBound pivotBound (F side) (E side) g (Dq side) S hcover hg0 (T side)
    (hlevels side) (hf side) (hsmall side) (hfmod side) R (hR side) hsmallR (hdistinct side)
    (hden side) a b
  dsimp only
  unfold movingReducedPairResidueCoefficient movingSeparatedPairResidueCoefficient
  rw [he false, he true]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInternalLocalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual internal-prime factors before averaging -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingInternalLocalSupport_iff {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (P : Finset ℕ)
    (hcover : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, value i ∈ P)
    (x y : ℤ) :
    (∀ p ∈ P, movingInternalLocalSupport value T p x y) ↔
      movingPrimeLineSupport value T x y ∧ movingSquareLineSupport value T x y := by
  have he (p : ℕ) (o : MovingSlotOccurrence σ) :
      squareReduction p
          (MovingSlotReversal.naturalReduction (p ^ 2) value (movingSlotLine o.path o.current).a *
            (x : ZMod (p ^ 2)) +
           MovingSlotReversal.naturalReduction (p ^ 2) value (movingSlotLine o.path o.current).b *
            (y : ZMod (p ^ 2))) =
        MovingSlotReversal.naturalReduction p value (movingSlotLine o.path o.current).a *
            (x : ZMod p) +
          MovingSlotReversal.naturalReduction p value (movingSlotLine o.path o.current).b *
            (y : ZMod p) := by
    simp
  constructor
  · intro h
    constructor
    · intro o ho i hi
      have hz := (h (value i) (hcover o ho i hi) o ho i hi rfl).1
      dsimp only at hz ⊢
      rw [he] at hz
      exact hz
    · intro o ho i hi
      exact (h (value i) (hcover o ho i hi) o ho i hi rfl).2
  · rintro ⟨hline, hsquare⟩ p _ o ho i hi rfl
    exact ⟨by simpa only [he] using hline o ho i hi, hsquare o ho i hi⟩

theorem movingInternalPairFactor_product {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (P : Finset ℕ)
    (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
      ∀ i ∈ o.current.compensationSlots, value i ∈ P) (x y : ℤ) :
    (∏ p ∈ P, movingInternalPairFactor value T p x y) =
      if ∀ side, movingPrimeLineSupport value (T side) x y ∧
        movingSquareLineSupport value (T side) x y then 1 else 0 := by
  have hiff : (∀ p ∈ P, ∀ side, movingInternalLocalSupport value (T side) p x y) ↔
      ∀ side, movingPrimeLineSupport value (T side) x y ∧
        movingSquareLineSupport value (T side) x y := by
    constructor
    · intro h side
      exact (movingInternalLocalSupport_iff value (T side) P (hcover side) x y).mp
        (fun p hp => h p hp side)
    · intro h p hp side
      exact (movingInternalLocalSupport_iff value (T side) P (hcover side) x y).mpr
        (h side) p hp
  by_cases h : ∀ p ∈ P, ∀ side, movingInternalLocalSupport value (T side) p x y
  · rw [ite_eq_left (hiff.mp h)]
    apply Finset.prod_eq_one
    intro p hp
    exact ite_eq_left (h p hp)
  · rw [ite_eq_right (fun hn => h (hiff.mpr hn))]
    obtain ⟨p, hp, hn⟩ := not_forall₂.mp h
    exact Finset.prod_eq_zero hp (ite_eq_right hn)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product of the frequency, internal-prime and spectator factors -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The coefficient of the literal original pair is a product over disjoint
arithmetic blocks. No Haar averaging or independence is assumed here. -/
theorem movingSeparatedPairResidueCoefficient_product {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (P : Finset ℕ)
    (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
      ∀ i ∈ o.current.compensationSlots, value i ∈ P) (x y : ℕ) :
    movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R x y =
      movingFrequencyPairFactor value outside F E T nodes R x y *
        (∏ p ∈ P, movingInternalPairFactor value T p x y) *
        ∏ i ∈ S, movingSpectatorPairFactor value (q i) (g i) (fun side => D side i) T x y := by
  have hint := movingInternalPairFactor_product value T P hcover (x : ℤ) (y : ℤ)
  simp only [Int.cast_natCast] at hint
  rw [hint]
  have hsplit : (∀ side, movingSeparatedSupport value outside (T side) (nodes side) R x y) ↔
      movingFrequencyPairSupport value outside T nodes R x y ∧
        (∀ side, movingPrimeLineSupport value (T side) x y ∧
          movingSquareLineSupport value (T side) x y) := by
    simp only [movingSeparatedSupport, movingFrequencyPairSupport, Bool.forall_bool]
    tauto
  have hprod : (∏ i ∈ S,
        movingSpectatorPairFactor value (q i) (g i) (fun side => D side i) T x y) =
      (∏ i ∈ S, movingModularSpectator value (q i) (g i) (D false i) (T false) x y) *
        conj (∏ i ∈ S, movingModularSpectator value (q i) (g i) (D true i) (T true) x y) := by
    simp only [movingSpectatorPairFactor, Finset.prod_mul_distrib, map_prod]
  rw [hprod]
  unfold movingSeparatedPairResidueCoefficient movingSeparatedResidueCoefficient
    movingFrequencyPairFactor
  by_cases h0 : movingSeparatedSupport value outside (T false) (nodes false) R x y
  · by_cases h1 : movingSeparatedSupport value outside (T true) (nodes true) R x y
    · have hall : ∀ side, movingSeparatedSupport value outside (T side) (nodes side) R x y := by
        simp only [Bool.forall_bool]; exact ⟨h0, h1⟩
      obtain ⟨hf, hi⟩ := hsplit.mp hall
      simp only [ite_eq_left h0, ite_eq_left h1, ite_eq_left hf, ite_eq_left hi, map_mul, Int.cast_natCast]
      ring
    · have hall : ¬ (movingFrequencyPairSupport value outside T nodes R x y ∧
          ∀ side, movingPrimeLineSupport value (T side) x y ∧
            movingSquareLineSupport value (T side) x y) := fun h => h1 (hsplit.mpr h true)
      by_cases hf : movingFrequencyPairSupport value outside T nodes R x y
      · have hi := fun hi => hall ⟨hf, hi⟩
        simp only [ite_eq_left h0, ite_eq_right h1, ite_eq_left hf, ite_eq_right hi,
          map_zero, mul_zero, zero_mul]
      · simp only [ite_eq_left h0, ite_eq_right h1, ite_eq_right hf,
          map_zero, mul_zero, zero_mul]
  · have hall : ¬ (movingFrequencyPairSupport value outside T nodes R x y ∧
        ∀ side, movingPrimeLineSupport value (T side) x y ∧
          movingSquareLineSupport value (T side) x y) := fun h => h0 (hsplit.mpr h false)
    by_cases hf : movingFrequencyPairSupport value outside T nodes R x y
    · have hi := fun hi => hall ⟨hf, hi⟩
      simp only [ite_eq_right h0, ite_eq_left hf, ite_eq_right hi, mul_zero, zero_mul]
    · simp only [ite_eq_right h0, ite_eq_right hf, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete CRT blocks for the original moving-history coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFrequencyPairFactor_modEq {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (hf : ∀ side, (T side).Frequencies (· ≠ 0))
    (hR : ∀ side, (T side).frequencyProduct ∣ R) (x y a b M : ℤ)
    (hM : R ^ (n + 1) ∣ M) (hx : x ≡ a [ZMOD M]) (hy : y ≡ b [ZMOD M]) :
    movingFrequencyPairFactor value outside F E T nodes R x y =
      movingFrequencyPairFactor value outside F E T nodes R a b := by
  have he (side : Bool) := movingFrequencyGate_modEq value R (T side) (hf side) (hR side)
    x y a b (hx.of_dvd hM) (hy.of_dvd hM)
  have hs : movingFrequencyPairSupport value outside T nodes R x y ↔
      movingFrequencyPairSupport value outside T nodes R a b := by
    simp only [movingFrequencyPairSupport, he]
  by_cases h : movingFrequencyPairSupport value outside T nodes R a b
  · simp only [movingFrequencyPairFactor, ite_eq_left (hs.mpr h), ite_eq_left h]
  · simp only [movingFrequencyPairFactor, ite_eq_right (fun hxy => h (hs.mp hxy)),
      ite_eq_right h]

/-- CRT coordinates are the casts of the original two residue representatives. -/
theorem crtExternalPairEquiv_casts {B : Type*} [Fintype B] (a : B → ℕ)
    [NeZero (∏ i, a i)] (hc : Pairwise (fun i j => (a i).Coprime (a j)))
    (z : ZMod (∏ i, a i) × (ZMod (∏ i, a i))ˣ) (i : B) :
    ((z.1.val : ZMod (a i)), ((z.2 : ZMod (∏ i, a i)).val : ZMod (a i))) =
      ((crtExternalPairEquiv a hc z i).1, ((crtExternalPairEquiv a hc z i).2 : ZMod (a i))) := by
  rcases z with ⟨x, y⟩
  rw [crtExternalPairEquiv_apply, crtUnitEquiv_apply, ZMod.prodEquivPi_apply]
  apply Prod.ext
  · have h := congrArg (ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i))
        (ZMod (a i))) (ZMod.natCast_zmod_val x)
    simpa only [map_natCast] using h
  · have h := congrArg (ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i))
        (ZMod (a i))) (ZMod.natCast_zmod_val (y : ZMod (∏ i, a i)))
    change ((y : ZMod (∏ i, a i)).val : ZMod (a i)) =
      (ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i)))
        (y : ZMod (∏ i, a i))
    simpa only [map_natCast] using h

/-- Complex-valued finite CRT factorization for the actual arithmetic blocks. -/
theorem movingArithmeticBlocks_average {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I)
    [∀ b, NeZero (movingArithmeticModuli r q P S b)]
    [NeZero (∏ b, movingArithmeticModuli r q P S b)]
    (hc : Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
      (movingArithmeticModuli r q P S c)))
    (f : ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ) :
    (Fintype.card (ZMod (∏ b, movingArithmeticModuli r q P S b) ×
      (ZMod (∏ b, movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ *
      (∑ z, ∏ b, f b (crtExternalPairEquiv (movingArithmeticModuli r q P S) hc z b)) =
    ∏ b, (Fintype.card (ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ * ∑ z, f b z := by
  let e := crtExternalPairEquiv (movingArithmeticModuli r q P S) hc
  rw [e.sum_comp (fun x => ∏ b, f b (x b)), Fintype.card_congr e, Fintype.card_pi]
  rw [← Fintype.prod_sum]
  simp only [Nat.cast_prod, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coprimality of the concrete arithmetic blocks -/

namespace Ostmann
open scoped Classical BigOperators

/-- The three arithmetic periods divide the concrete CRT modulus. -/
theorem movingArithmeticModuli_periods {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I) (R : ℤ) (k : ℕ) (hR : R ^ k ∣ (r : ℤ)) :
    (R ^ k ∣ ((∏ b, movingArithmeticModuli r q P S b : ℕ) : ℤ)) ∧
    (∀ p ∈ P, (p ^ 2 : ℤ) ∣ ((∏ b, movingArithmeticModuli r q P S b : ℕ) : ℤ)) ∧
    (∀ i ∈ S, (q i : ℤ) ∣ ((∏ b, movingArithmeticModuli r q P S b : ℕ) : ℤ)) := by
  constructor
  · apply hR.trans
    exact_mod_cast (Finset.dvd_prod_of_mem (movingArithmeticModuli r q P S)
      (Finset.mem_univ (Sum.inl ())))
  constructor
  · intro p hp
    have h : p ^ 2 ∣ ∏ b, movingArithmeticModuli r q P S b :=
      Finset.dvd_prod_of_mem (movingArithmeticModuli r q P S)
        (Finset.mem_univ (Sum.inr (Sum.inl (⟨p, hp⟩ : P))))
    exact_mod_cast h
  · intro i hi
    have h : q i ∣ ∏ b, movingArithmeticModuli r q P S b :=
      Finset.dvd_prod_of_mem (movingArithmeticModuli r q P S)
        (Finset.mem_univ (Sum.inr (Sum.inr (⟨i, hi⟩ : S))))
    exact_mod_cast h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageRegularAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained Page term in the actual regular-prime average -/

namespace Ostmann
open scoped Classical BigOperators

theorem pageGiantWeight_modEq (P : PublishedProgressionInput) (Q r a b : ℕ)
    (h : Nat.ModEq r a b) (y : ℝ) :
    pageGiantWeight P Q r a y = pageGiantWeight P Q r b y := by
  simp only [pageGiantWeight, pageMultiplier, pageCoefficient_eq_of_modEq _ h]

theorem periodic_coefficient_regular_page_average {I : Type*} [Fintype I] [DecidableEq I]
    (P : PublishedProgressionInput) (Q : ℕ)
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (hpage : pageAtModulus ((∏ i, p i) * r) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i))
    (hs : ∀ i, (s : ZMod (p i)) ≠ 0) (ho : ∀ i, other i ≠ 0)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (C : ℕ → ℕ → ℂ)
    (hC : ∀ a b d e, Nat.ModEq r a d → Nat.ModEq r b e → C a b = C d e) (y : ℝ) :
    correctedMixedPairAverage P Q ((∏ i, p i) * r)
      (fun a b => C a b * (guardedRegularMultiplier p active s other g a b : ℂ)) y =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        correctedMixedPairAverage P Q r C y := by
  have he := periodic_coefficient_regular_average p hc r hcop active s other hs ho g hg henergy
    (fun a b => C a b * pageGiantWeight P Q r b y)
    (fun a b d e ha hb => by rw [hC a b d e ha hb, pageGiantWeight_modEq P Q r b e hb y])
  change _ = _ at he
  convert he using 1
  · unfold correctedMixedPairAverage
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    simp only [pageGiantWeight, hpage]
    ring
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedCRT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact CRT factorization of the original separated pair -/

namespace Ostmann
open scoped Classical BigOperators

section
variable {σ I : Type*} (q : I → ℕ) [∀ i, Fact (q i).Prime]
  (value : σ → ℕ) (outside : List ℕ)
  (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
  (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
  (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
  {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
  (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) (S : Finset I)
  [NeZero (∏ b, movingArithmeticModuli r q P S b)]
  (hf : ∀ side, (T side).Frequencies (· ≠ 0))
  (hR : ∀ side, (T side).frequencyProduct ∣ R)
  (hfrequency : R ^ (n + 1) ∣ (r : ℤ))
  (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
    ∀ i ∈ o.current.compensationSlots, value i ∈ P)
  (hc : Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
    (movingArithmeticModuli r q P S c)))

include hf hR hfrequency hcover hc

/-- Pointwise CRT identification, using the actual frequency recursion and
all actual internal occurrences, before any norm or average is taken. -/
theorem movingSeparatedPairResidueCoefficient_crt
    (z : ZMod (∏ b, movingArithmeticModuli r q P S b) ×
      (ZMod (∏ b, movingArithmeticModuli r q P S b))ˣ) :
    movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R
      z.1.val (z.2 : ZMod (∏ b, movingArithmeticModuli r q P S b)).val =
    ∏ b, movingArithmeticLocalFactor q value outside F E g D T nodes R r P S b
      (crtExternalPairEquiv (movingArithmeticModuli r q P S) hc z b) := by
  let a := movingArithmeticModuli r q P S
  let e := crtExternalPairEquiv a hc
  let f := movingArithmeticLocalFactor q value outside F E g D T nodes R r P S
  let x := z.1.val
  let y := (z.2 : ZMod (∏ b, a b)).val
  have hcasts (b) := crtExternalPairEquiv_casts a hc z b
  have hfreq : f (.inl ()) (e z (.inl ())) =
      movingFrequencyPairFactor value outside F E T nodes R x y := by
    let v : ZMod r × (ZMod r)ˣ := e z (.inl ())
    have hl : (x : ZMod r) = v.1 := congrArg Prod.fst (hcasts (.inl ()))
    have hr : (y : ZMod r) = (v.2 : ZMod r) := congrArg Prod.snd (hcasts (.inl ()))
    have hx : (x : ℤ) ≡ (v.1.val : ℤ) [ZMOD (r : ℤ)] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ r).mp
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
        hl
    have hy : (y : ℤ) ≡ ((v.2 : ZMod r).val : ℤ) [ZMOD (r : ℤ)] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ r).mp
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
        hr
    exact (movingFrequencyPairFactor_modEq value outside F E T nodes R hf hR
      x y v.1.val (v.2 : ZMod r).val r hfrequency hx hy).symm
  have hint (p : P) : f (.inr (.inl p)) (e z (.inr (.inl p))) =
      movingInternalPairFactor value T p.val x y := by
    have hl : (x : ZMod (p.val ^ 2)) = (e z (.inr (.inl p))).1 :=
      congrArg Prod.fst (hcasts (.inr (.inl p)))
    have hr : (y : ZMod (p.val ^ 2)) =
        (show (ZMod (p.val ^ 2))ˣ from (e z (.inr (.inl p))).2).val :=
      congrArg Prod.snd (hcasts (.inr (.inl p)))
    exact congrArg₂ (movingInternalPairFactor value T p.val) hl.symm hr.symm
  have hspec (i : S) : f (.inr (.inr i)) (e z (.inr (.inr i))) =
      movingSpectatorPairFactor value (q i.val) (g i.val) (fun side => D side i.val) T x y := by
    have hl : (x : ZMod (q i.val)) = (e z (.inr (.inr i))).1 :=
      congrArg Prod.fst (hcasts (.inr (.inr i)))
    have hr : (y : ZMod (q i.val)) =
        (show (ZMod (q i.val))ˣ from (e z (.inr (.inr i))).2).val :=
      congrArg Prod.snd (hcasts (.inr (.inr i)))
    exact congrArg₂ (movingSpectatorPairFactor value (q i.val) (g i.val)
      (fun side => D side i.val) T) hl.symm hr.symm
  change movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R x y =
    ∏ b, f b (e z b)
  rw [movingSeparatedPairResidueCoefficient_product q value outside F E g D S T nodes R P hcover]
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, hfreq, hint, hspec]
  rw [Finset.prod_coe_sort P (fun p => movingInternalPairFactor value T p x y),
    Finset.prod_coe_sort S (fun i =>
      movingSpectatorPairFactor value (q i) (g i) (fun side => D side i) T x y)]
  ring

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedPageCRT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining the Page correction in the frequency block -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingArithmeticPageFactor_product {I : Type*}
    (r : ℕ) (q : I → ℕ) (P : Finset ℕ) (S : Finset I)
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
    (f : ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ → ℂ)
    (v : ∀ b, ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) :
    (∏ b, movingArithmeticPageFactor r q P S input Q y f b (v b)) =
      (∏ b, f b (v b)) *
        pageGiantWeight input Q r
          (show (ZMod r)ˣ from (v (.inl ())).2).val.val y := by
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, movingArithmeticPageFactor]
  ring

section
variable {σ I : Type*} (q : I → ℕ) [∀ i, Fact (q i).Prime]
  (value : σ → ℕ) (outside : List ℕ)
  (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
  (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
  (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
  {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
  (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) (S : Finset I)
  [∀ b, NeZero (movingArithmeticModuli r q P S b)]
  [NeZero (∏ b, movingArithmeticModuli r q P S b)]
  (hf : ∀ side, (T side).Frequencies (· ≠ 0))
  (hR : ∀ side, (T side).frequencyProduct ∣ R)
  (hfrequency : R ^ (n + 1) ∣ (r : ℤ))
  (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
    ∀ i ∈ o.current.compensationSlots, value i ∈ P)
  (hc : Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
    (movingArithmeticModuli r q P S c)))
  (input : PublishedProgressionInput) (Q : ℕ)
  (hpage : pageAtModulus (∏ b, movingArithmeticModuli r q P S b) (selectedPageZero input Q) =
    pageAtModulus r (selectedPageZero input Q))

include hf hR hfrequency hcover hc hpage

/-- The original Page-weighted mixed average factors exactly. Its Page term
stays in the frequency factor, with no absolute value or mean replacement. -/
theorem movingSeparatedPairResidueCoefficient_page_average (y : ℝ) :
    correctedMixedPairAverage input Q (∏ b, movingArithmeticModuli r q P S b)
      (movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R) y =
    ∏ b, (Fintype.card (ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ *
      ∑ z, movingArithmeticPageFactor r q P S input Q y
        (movingArithmeticLocalFactor q value outside F E g D T nodes R r P S) b z := by
  let a := movingArithmeticModuli r q P S
  let e := crtExternalPairEquiv a hc
  let f := movingArithmeticLocalFactor q value outside F E g D T nodes R r P S
  let fP := movingArithmeticPageFactor r q P S input Q y f
  have hpageA : pageAtModulus (∏ b, a b) (selectedPageZero input Q) =
      pageAtModulus r (selectedPageZero input Q) := hpage
  have he (z : ZMod (∏ b, a b) × (ZMod (∏ b, a b))ˣ) :
      movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R
          z.1.val (z.2 : ZMod (∏ b, a b)).val *
        pageGiantWeight input Q (∏ b, a b) (z.2 : ZMod (∏ b, a b)).val y =
      ∏ b, fP b (e z b) := by
    have hcast := crtExternalPairEquiv_casts a hc z (.inl ())
    let v : ZMod r × (ZMod r)ˣ := e z (.inl ())
    have hm : Nat.ModEq r (z.2 : ZMod (∏ b, a b)).val (v.2 : ZMod r).val := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      have hh : ((z.2 : ZMod (∏ b, a b)).val : ZMod r) = (v.2 : ZMod r) :=
        congrArg Prod.snd hcast
      simpa only [ZMod.natCast_zmod_val] using hh
    have hp : pageGiantWeight input Q (∏ b, a b) (z.2 : ZMod (∏ b, a b)).val y =
        pageGiantWeight input Q r (v.2 : ZMod r).val y := by
      calc
        _ = pageGiantWeight input Q r (z.2 : ZMod (∏ b, a b)).val y := by
          simp only [pageGiantWeight, hpageA]
        _ = _ := pageGiantWeight_modEq input Q r _ _ hm y
    rw [movingSeparatedPairResidueCoefficient_crt q value outside F E g D T nodes
      R r P S hf hR hfrequency hcover hc, hp]
    exact (movingArithmeticPageFactor_product r q P S input Q y f (e z)).symm
  unfold correctedMixedPairAverage
  calc
    _ = (Fintype.card (ZMod (∏ b, a b) × (ZMod (∏ b, a b))ˣ) : ℂ)⁻¹ *
        (∑ z, ∏ b, fP b (e z b)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      exact he z
    _ = _ := movingArithmeticBlocks_average r q P S hc fP

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedAverages
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit three-factor form of the original Page-weighted average -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingArithmeticPageFactor_averages {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) (S : Finset I)
    [∀ p : P, Fact p.val.Prime] [∀ b, NeZero (movingArithmeticModuli r q P S b)]
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    (∏ b, (Fintype.card (ZMod (movingArithmeticModuli r q P S b) ×
      (ZMod (movingArithmeticModuli r q P S b))ˣ) : ℂ)⁻¹ *
      ∑ z, movingArithmeticPageFactor r q P S input Q y
        (movingArithmeticLocalFactor q value outside F E g D T nodes R r P S) b z) =
      movingFrequencyPageAverage value outside F E T nodes R r input Q y *
        (∏ p : P, movingInternalHaarAverage value T p.val) *
        ∏ i : S, movingSpectatorHaarAverage value (q i.val) (g i.val)
          (fun side => D side i.val) T := by
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, movingArithmeticPageFactor,
    movingArithmeticLocalFactor, movingArithmeticModuli, movingFrequencyPageAverage,
    movingInternalHaarAverage, movingSpectatorHaarAverage]
  rw [← mul_assoc]
  congr 4

section
variable {σ I : Type*} (q : I → ℕ) [∀ i, Fact (q i).Prime]
  (value : σ → ℕ) (outside : List ℕ)
  (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
  (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
  (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ)
  {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
  (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) (S : Finset I)
  [∀ p : P, Fact p.val.Prime]
  [∀ b, NeZero (movingArithmeticModuli r q P S b)]
  [NeZero (∏ b, movingArithmeticModuli r q P S b)]
  (hf : ∀ side, (T side).Frequencies (· ≠ 0))
  (hR : ∀ side, (T side).frequencyProduct ∣ R)
  (hfrequency : R ^ (n + 1) ∣ (r : ℤ))
  (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
    ∀ i ∈ o.current.compensationSlots, value i ∈ P)
  (hc : Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
    (movingArithmeticModuli r q P S c)))
  (input : PublishedProgressionInput) (Q : ℕ)
  (hpage : pageAtModulus (∏ b, movingArithmeticModuli r q P S b) (selectedPageZero input Q) =
    pageAtModulus r (selectedPageZero input Q))

include hf hR hfrequency hcover hc hpage

theorem movingSeparatedPairResidueCoefficient_page_factorization (y : ℝ) :
    correctedMixedPairAverage input Q (∏ b, movingArithmeticModuli r q P S b)
      (movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R) y =
      movingFrequencyPageAverage value outside F E T nodes R r input Q y *
        (∏ p : P, movingInternalHaarAverage value T p.val) *
        ∏ i : S, movingSpectatorHaarAverage value (q i.val) (g i.val)
          (fun side => D side i.val) T := by
  rw [movingSeparatedPairResidueCoefficient_page_average q value outside F E g D T nodes
    R r P S hf hR hfrequency hcover hc input Q hpage]
  exact movingArithmeticPageFactor_averages q value outside F E g D T nodes R r P S input Q y

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compensation coincidences vanish on both original and arithmetic support -/

namespace Ostmann
open scoped Classical

theorem movingRegularOutsidePairwise_root {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (h : movingRegularOutsidePairwise value outside T) :
    (T.regularSlots.map value).Pairwise Nat.Coprime := by
  have hr : (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
    cases T with
    | leaf => exact h
    | node => exact h.1
  exact (List.pairwise_append.mp hr).1

theorem movingFullOutsidePairwise_regular {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (h : movingFullOutsidePairwise value outside T XL XR) :
    movingRegularOutsidePairwise value outside T := by
  induction T generalizing XL XR with
  | leaf s regular =>
    exact h.tail.tail
  | node s CL CR U left right ihL ihR =>
    exact ⟨h.1.tail.tail, ihL _ _ h.2.1, ihR _ _ h.2.2⟩

theorem MovingSlotData.compensationDistinct_of_regularSupport {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hc : T.RegularCoherent) (h : movingRegularOutsidePairwise value outside T) :
    T.CompensationDistinct value := by
  induction T with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    have hp := movingRegularOutsidePairwise_root value outside left h.2.1
    have hperm := (hc.1.map value).pairwise_iff (R := Nat.Coprime) (fun h => h.symm)
    have hu : ((U ++ CL).map value).Pairwise Nat.Coprime := hperm.mp hp
    rw [List.map_append] at hu
    exact ⟨(List.pairwise_append.mp hu).1, ihL hc.2.2.1 h.2.1,
      ihR hc.2.2.2 h.2.2⟩

theorem movingSupportedWeight_zero_of_compensation_collision {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hc : T.RegularCoherent) (hbad : ¬ T.CompensationDistinct value)
    (XL XR : ℕ) (z : ℂ) : movingSupportedWeight value outside T XL XR z = 0 := by
  apply ite_eq_right
  intro h
  exact hbad (T.compensationDistinct_of_regularSupport value outside hc
    (movingFullOutsidePairwise_regular value outside T XL XR h.1))

theorem MovingSlotData.compensationPrimeData_of_units {σ : Type*}
    (value : σ → ℕ) (hprime : ∀ i, (value i).Prime) {n : ℕ} (T : MovingSlotData σ n)
    (hu : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hd : T.CompensationDistinct value) : T.CompensationPrimeData value := by
  induction T with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    refine ⟨?_, hd.1, ?_, ihL (fun i => (hu i).2.1) hd.2.1,
      ihR (fun i => (hu i).2.2) hd.2.2⟩
    · intro p hp
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      exact hprime i
    · intro p hp
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      apply (hprime i).coprime_iff_not_dvd.mp
      have h := (hu i).1
      change IsCoprime s (value i : ℤ) at h
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] at h
      exact Nat.coprime_comm.mp h

theorem movingSeparatedResidueCoefficient_zero_of_compensation_collision {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (R x y : ℤ)
    (hc : T.RegularCoherent) (hbad : ¬ T.CompensationDistinct value) :
    movingSeparatedResidueCoefficient q value outside F E g D S T nodes R x y = 0 := by
  apply ite_eq_right
  intro h
  exact hbad (T.compensationDistinct_of_regularSupport value outside hc h.1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingHarmonicSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete support conditions for the original harmonic role priors -/

namespace Ostmann
open scoped Classical BigOperators

/-- A nonzero original frequency smaller than an internal prime remains
nonzero modulo that prime. -/
theorem intCast_ne_zero_of_natAbs_lt (q : ℕ) (s : ℤ) (hs : s ≠ 0)
    (hqs : s.natAbs < q) : (s : ZMod q) ≠ 0 := by
  intro hz
  have hd : q ∣ s.natAbs := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd s q).mp hz
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr hh
  exact (not_le_of_gt hqs) (Nat.le_of_dvd (Int.natAbs_pos.mpr hs) hd)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLeafAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar leaf weights retain the actual frequency cutoff -/

namespace Ostmann
open scoped Classical

/-- Removing the explicit compensation multipliers leaves a scalar amplitude
of norm at most one whenever the actual leaf coefficients have that bound. -/
theorem movingDataWeight_unit_norm_le_one {σ : Type*}
    (F : {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (hF : ∀ s regular, ‖F (.leaf s regular) s‖ ≤ 1)
    {n : ℕ} (T : MovingSlotData σ n) :
    ‖movingDataWeight F (fun _ _ _ _ => 1) T‖ ≤ 1 := by
  induction T with
  | leaf s regular => exact hF s regular
  | node s CL CR U l r ihL ihR =>
    simp only [movingDataWeight, Complex.ofReal_one, one_mul, norm_mul, norm_star]
    exact (mul_le_mul ihL ihR (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorBulkScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The even bulk size and the accumulated giant loss in Section 9 -/

namespace Ostmann
open Filter
open scoped BigOperators

theorem spectatorBulkCount_upper (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (spectatorBulkCount k L : ℝ) ≤ (k : ℝ) ^ 4 * L := by
  have h := Nat.floor_le (show 0 ≤ (k : ℝ) ^ 4 * L / 2 by positivity)
  unfold spectatorBulkCount
  push_cast
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-depth cost of the actual sharp pattern kernel -/

namespace Ostmann
open scoped SchwartzMap

theorem movingFourierVariationBudget_nonneg (ψ : 𝓢(ℝ, ℂ))
    (V lo hi : ℝ) (n : ℕ) (hV : 0 ≤ V) (hhi : lo ≤ hi) :
    0 ≤ movingFourierVariationBudget ψ V lo hi n := by
  have hB := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD := schwartz_profile_lip_nonneg ψ
  have hW := sub_nonneg.mpr hhi
  unfold movingFourierVariationBudget
  positivity

theorem movingPatternKernelBudget_exp_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A H B D : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) →
      bulkKernelPairComparisonBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D ≤
      Real.exp (C * ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hV⟩ := movingFourierVariationBudget_exp_window ψ n A H hA hH
  let c := (2 ^ n + (2 ^ n - 1)) + (3 * (2 ^ n - 1) + 2 * 2 ^ n)
  let a := 2 * c * (2 * n + 1) * 2 ^ n
  let b := 2 * c * (2 * n * (2 ^ n * (r₀ + 4 * n + 4)) +
    2 ^ n * (r₀ + 4 * n)) + 1
  let K : ℝ := a + b
  let H : ℝ := ((2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hK : 0 < K := by dsimp only [K, b]; positivity
  have hH : 0 ≤ H := sq_nonneg _
  refine ⟨K + 2 * C + H, by positivity, ?_⟩
  intro m lo hi hhi hwidth
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hcount :
      2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * (2 ^ n * (r₀ + m + 4 * n + 4)) + 0) +
        2 ^ n * (r₀ + m + 4 * n))) +
        ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * (2 ^ n * (r₀ + m + 4 * n + 4)) + 0) +
        2 ^ n * (r₀ + m + 4 * n)))) + 1 = a * m + b := by
    dsimp only [a, b, c]
    ring
  have hroot : ((a * m + b : ℕ) : ℝ) ≤ Real.exp (K * ((m : ℝ) + 1)) := by
    have hab : ((a * m + b : ℕ) : ℝ) ≤ K * ((m : ℝ) + 1) := by
      push_cast
      dsimp only [K]
      nlinarith [mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) hm]
    exact hab.trans (by linarith [Real.add_one_le_exp (K * ((m : ℝ) + 1))])
  have hv0 := movingFourierVariationBudget_nonneg ψ (Real.exp (A * m)) lo hi n
    (Real.exp_nonneg _) hhi
  have hv2 := pow_le_pow_left₀ hv0 (hV m hm lo hi hhi hwidth) 2
  have hh : H ≤ Real.exp (H * ((m : ℝ) + 1)) := by
    have : H ≤ H * ((m : ℝ) + 1) := by nlinarith [mul_nonneg hH hm]
    exact this.trans (by linarith [Real.add_one_le_exp (H * ((m : ℝ) + 1))])
  unfold bulkKernelPairComparisonBudget
  rw [hcount, mul_pow]
  change ((a * m + b : ℕ) : ℝ) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n ^ 2 * H) ≤ _
  calc
    _ ≤ Real.exp (K * ((m : ℝ) + 1)) *
        ((Real.exp (C * ((m : ℝ) + 1))) ^ 2 * Real.exp (H * ((m : ℝ) + 1))) := by
      gcongr
    _ = Real.exp ((K + 2 * C + H) * ((m : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem movingPatternKernelBudget_spectatorScale_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H B D : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ lo hi : ℝ, lo ≤ hi → hi - lo ≤ Real.exp (H * m) →
      bulkKernelPairComparisonBudget ψ (Real.exp (A * m)) lo hi n
        (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D ≤
      Real.exp (C * L ^ 2) := by
  obtain ⟨C, hC, hb⟩ := movingPatternKernelBudget_exp_window ψ n r₀ A H B D hA hH
  refine ⟨C * ((k : ℝ) ^ 4 + 1) + 1, ?_, ?_⟩
  · have : 0 ≤ C * ((k : ℝ) ^ 4 + 1) := by positivity
    linarith
  intro L hL
  dsimp only
  intro lo hi hhi hwidth
  apply (hb _ lo hi hhi hwidth).trans
  apply Real.exp_le_exp.mpr
  have hL0 : 0 ≤ L := by linarith
  have hm := spectatorBulkCount_upper k L hL0
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hscale : (spectatorBulkCount k L : ℝ) + 1 ≤ ((k : ℝ) ^ 4 + 1) * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hLsq (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)
    nlinarith
  have := mul_le_mul_of_nonneg_left hscale hC.le
  nlinarith [sq_nonneg L]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternKernelGain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quartet gain absorbs the actual sharp-kernel main term -/

namespace Ostmann
open scoped SchwartzMap

theorem bulkKernelPair_smooth_le_budget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r e : ℕ) (B D : ℝ) :
    (movingFourierVariationBudget ψ V lo hi n *
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
    bulkKernelPairComparisonBudget ψ V lo hi n d r e B D := by
  let c := 2 * (((2 ^ n + (2 ^ n - 1)) * (2 * (n * d + e) + r)) +
    ((3 * (2 ^ n - 1) + 2 * 2 ^ n) * (2 * (n * d + e) + r)))
  have hc : (1 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 c
  exact le_mul_of_one_le_left (sq_nonneg _) hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSpectatorCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise cost of the actual normalized spectator transforms -/

namespace Ostmann
open scoped Classical BigOperators

/-- A common prime upper bound controls all actual pointwise spectator
factors. This cost is retained in the cell error, separate from signed gain. -/
theorem moving_spectator_product_cost (n m : ℕ) (p : Fin m → ℕ)
    (V : ℝ) (hp : ∀ i, (p i : ℝ) ≤ Real.exp V) :
    (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp ((2 ^ (n + 1) : ℕ) * (m : ℝ) * V) := by
  calc
    _ ≤ ∏ _i : Fin m, (Real.exp V) ^ (2 ^ (n + 1)) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hp i) _
    _ = _ := by
      simp only [← Real.exp_nat_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      ring

theorem moving_spectator_linear_cost (n m : ℕ) (p : Fin m → ℕ)
    (K L A : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (_hA : 0 ≤ A)
    (hm : (m : ℝ) ≤ K * L) (hamp : A ≤ Real.exp (K * L))
    (hp : ∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) :
    A * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K * L *
        Real.exp ((1 / 1000 : ℝ) * L)) := by
  have hE : 1 ≤ Real.exp ((1 / 1000 : ℝ) * L) :=
    Real.one_le_exp_iff.mpr (by positivity)
  calc
    _ ≤ Real.exp (K * L) *
        Real.exp ((2 ^ (n + 1) : ℕ) * (m : ℝ) * Real.exp ((1 / 1000 : ℝ) * L)) :=
      mul_le_mul hamp (moving_spectator_product_cost n m p _ hp)
        (Finset.prod_nonneg fun i _ => by positivity) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (2 ^ (n + 1))))
        (Real.exp_nonneg ((1 / 1000 : ℝ) * L))
      have hKL := mul_le_mul_of_nonneg_left hE (mul_nonneg hK hL)
      nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternGiantVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform giant variation cost at the selected-prime scales -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingFourierVariationBudget_mono_frequency (ψ : 𝓢(ℝ, ℂ))
    (V W lo hi : ℝ) (n : ℕ) (hV : 0 ≤ V) (hVW : V ≤ W) (hhi : lo ≤ hi) :
    movingFourierVariationBudget ψ V lo hi n ≤ movingFourierVariationBudget ψ W lo hi n := by
  have hB := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD := schwartz_profile_lip_nonneg ψ
  have hwidth := sub_nonneg.mpr hhi
  unfold movingFourierVariationBudget
  gcongr

/-- The complete pointwise cost needed for both giant integrations is bounded
before choosing the Fourier window, its frequencies, or the spectator primes. -/
theorem movingPattern_pointwise_cost_budget (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin B D : ℝ) (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (V lo hi : ℝ), 0 ≤ V → V ≤ Real.exp (A * m) →
      lo ≤ hi → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 *
          (movingFourierVariationBudget ψ V lo hi n *
            (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
  obtain ⟨Cw, hCw, hkernel⟩ := movingPatternKernelBudget_spectatorScale_window
    ψ n r₀ k A Wwin B D hA hWwin
  let K := (k : ℝ) ^ 4 + 4
  let Cs := (((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K
  let C := max Cw Cs
  have hK : 4 ≤ K := by
    dsimp only [K]
    linarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4]
  have hCwC : Cw ≤ C := le_max_left _ _
  have hCsC : Cs ≤ C := le_max_right _ _
  refine ⟨C, hCw.trans hCwC, ?_⟩
  intro L hL
  dsimp only
  intro p V lo hi hV hVA hhi hwidth hp
  let m := spectatorBulkCount k L
  have hL0 : 0 ≤ L := by linarith
  have hm : (m : ℝ) ≤ K * L := (spectatorBulkCount_upper k L hL0).trans
    (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) hL0)
  have hKL : 4 ≤ K * L := by nlinarith
  have hamp : (4 : ℝ) ≤ Real.exp (K * L) := by
    linarith [Real.add_one_le_exp (K * L)]
  have hspec := moving_spectator_linear_cost n m p K L 4 (by linarith) hL0 (by norm_num) hm hamp hp
  have hprod : (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 = ∏ i, (p i : ℝ) ^ (2 ^ (n + 1)) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, pow_succ]
  have hspec' : 4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 ≤
      Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    rw [hprod]
    apply hspec.trans
    apply Real.exp_le_exp.mpr
    change Cs * L * Real.exp ((1 / 1000 : ℝ) * L) ≤ _
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hCsC hL0
    · exact Real.exp_le_exp.mpr (by nlinarith)
    · exact Real.exp_nonneg _
    · exact mul_nonneg (by linarith [hCw.trans hCwC]) hL0
  have hvar := movingFourierVariationBudget_mono_frequency ψ V (Real.exp (A * m)) lo hi n hV hVA hhi
  have hsmooth :
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
      Real.exp (C * L ^ 2) := by
    have hpow :
        (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (movingFourierVariationBudget_nonneg ψ V lo hi n hV hhi) hvar 2)
        (sq_nonneg _)
    exact hpow.trans ((bulkKernelPair_smooth_le_budget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D).trans
      ((hkernel L hL lo hi hhi hwidth).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCwC (sq_nonneg L)))))
  calc
    _ ≤ Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) * Real.exp (C * L ^ 2) :=
      mul_le_mul hspec' hsmooth (sq_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOuterVariationScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The moving-window budget for the original outer-prior kernel -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The two original outer factors and the diagonal reciprocal ratio cost
only a fixed constant, uniformly in the giant cell centers. -/
theorem movingOuterVariationBudget_bound (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n : ℕ) (B D : ℝ) (diagonal : Bool) :
    2 * giantOuterScalar diagonal * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
      (2 * Real.exp 1 * (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (3 + Real.exp 2)) *
        (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hcoef : 2 * giantOuterScalar diagonal * (if diagonal then 1 + Real.exp 2 else 2) ≤
      2 * Real.exp 1 * (3 + Real.exp 2) := by
    have hp := mul_nonneg (Real.exp_nonneg (1 : ℝ)) (Real.exp_nonneg (2 : ℝ))
    cases diagonal <;> simp only [giantOuterScalar, Bool.false_eq_true, ite_false, if_false, ite_true, if_true] <;>
      nlinarith only [he, hp, Real.exp_pos (1 : ℝ)]
  have hh := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (sq_nonneg (2 * B + D * (Real.exp 2 - 1)))
      (sq_nonneg (movingFourierVariationBudget ψ V lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1))))
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ((try unfold movingOuterVariationBudget) <;> ring)

/-- Actual spectator growth, bounded harmonic normalizers and every moving
bottom window fit the common giant comparison budget. -/
theorem moving_outer_variation_scale (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin B D H : ℝ) (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hH : 0 ≤ H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (V lo hi amp : ℝ) (diagonal : Bool),
      0 ≤ V → V ≤ Real.exp (A * m) → lo ≤ hi → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      0 ≤ amp → amp ≤ 4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 * Real.exp (H * L + H * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      2 * (amp * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ 2 + C * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
  obtain ⟨C₀, hC₀, hbase⟩ := movingPattern_pointwise_cost_budget ψ n r₀ k A Wwin B D hA hWwin
  let F := 2 * Real.exp 1 * (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (3 + Real.exp 2)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  let C := C₀ + H + F
  have hC : C₀ ≤ C := by dsimp only [C]; linarith only [hH, hF]
  refine ⟨C, hC₀.trans hC, ?_⟩
  intro L hL
  dsimp only
  intro p V lo hi amp diagonal hV hVA hhi hwidth hp hamp hampup
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have houter := movingOuterVariationBudget_bound ψ V lo hi n B D diagonal
  have hbase' := hbase L hL p V lo hi hV hVA hhi hwidth hp
  let W := (movingFourierVariationBudget ψ V lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hFE : F ≤ Real.exp (F * L) := by
    have hh := mul_le_mul_of_nonneg_left hL hF
    linarith only [hh, Real.add_one_le_exp (F * L)]
  have hbound :
      2 * (amp * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C₀ * L ^ 2 + C₀ * L * Real.exp ((1 / 1000 : ℝ) * L)) *
          Real.exp ((H + F) * L + H * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    calc
      _ = amp * (2 * giantOuterScalar diagonal * movingOuterVariationBudget ψ V lo hi n B D diagonal) := by ring
      _ ≤ amp * (F * W) := mul_le_mul_of_nonneg_left houter hamp
      _ ≤ (4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 * Real.exp (H * L + H * L * Real.exp ((12 / 1000 : ℝ) * L))) * (F * W) :=
        mul_le_mul_of_nonneg_right hampup (mul_nonneg hF (sq_nonneg _))
      _ = (4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 * W) * (F * Real.exp (H * L + H * L * Real.exp ((12 / 1000 : ℝ) * L))) := by ring
      _ ≤ Real.exp (C₀ * L ^ 2 + C₀ * L * Real.exp ((1 / 1000 : ℝ) * L)) *
          (Real.exp (F * L) * Real.exp (H * L + H * L * Real.exp ((12 / 1000 : ℝ) * L))) :=
        mul_le_mul hbase' (mul_le_mul_of_nonneg_right hFE (Real.exp_nonneg _))
          (mul_nonneg hF (Real.exp_nonneg _)) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  apply hbound.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hLsq : L ≤ L ^ 2 := by nlinarith only [hL]
  have hpoly := mul_le_mul_of_nonneg_left hLsq (add_nonneg hH hF)
  have hscale : Real.exp ((1 / 1000 : ℝ) * L) ≤ Real.exp ((12 / 1000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith only [hL0])
  have hterm := mul_le_mul_of_nonneg_left hscale
    (mul_nonneg (le_trans (by norm_num) hC₀) hL0)
  have hextra := mul_nonneg (mul_nonneg hF hL0)
    (Real.exp_nonneg ((12 / 1000 : ℝ) * L))
  dsimp only [C] at ⊢
  nlinarith only [hpoly, hterm, hextra]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternArithmeticData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic support of the actual finite pattern trees -/

namespace Ostmann
open scoped Classical

theorem movingPatternFinBulkData_regular_coherent {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
    (b : Bool) : (movingPatternFinBulkData e n m t small slot perm pattern b).RegularCoherent := by
  rw [movingPatternFinBulkData_build]
  exact buildMovingSlotData_regular_coherent _ _ _ _ _

/-- Every compensation prime comes from an internal equality class. The
strict level separation excludes all external regular slots. -/
theorem movingPatternFinBulkData_internal_cover {A B C : Type*} [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ j, n ≤ tierB j) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (value : A → ℕ) (x : Fin (N + 1) → A) :
    ∀ b, ∀ o ∈ (movingPatternFinBulkData e n m t small slot perm pattern b).occurrences,
      ∀ i ∈ o.current.compensationSlots,
        value (x i) ∈ Finset.univ.image (fun c : C => value (x (e.symm (.inr c)))) := by
  intro b o ho i hi
  let tier := (Sum.elim tierB tierC) ∘ e
  let T := movingPatternFinBulkData e n m t small slot perm pattern b
  have hlevels : T.Levels tier :=
    movingPatternFinBulkData_levels e tierB tierC n m t small slot perm pattern hB htier b
  have hlt := T.occurrence_compensation_level tier hlevels o ho i hi
  have hbound := (T.occurrence_bounds tier hlevels o ho).2.1
  have hiN : tier i < n := lt_of_lt_of_le hlt (by omega)
  cases he : e i with
  | inl j =>
    have hj := hB j
    simp only [tier, Function.comp_apply, he, Sum.elim_inl] at hiN
    omega
  | inr c =>
    apply Finset.mem_image.mpr
    refine ⟨c, Finset.mem_univ _, ?_⟩
    have hh := e.symm_apply_apply i
    rw [he] at hh
    rw [hh]

/-- Both histories have the same top regular product. No sampled internal
prime or history frequency enters this product. -/
theorem movingPatternFinBulkData_regular_product {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C) (value : Fin (N + 1) → ℕ) (b : Bool) :
    MovingSlotReversal.naturalProduct value
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern b).regularSlots =
    MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
        flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))) := by
  rw [movingPatternFinBulkData_build]
  have hp := buildMovingSlotData_regular_perm n (t b)
    (movingPatternFiniteSmall e n small)
    (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))
    (movingPatternFiniteSamples e n pattern b)
  have he : (if b then bulkSlotLeaves n m (movingPatternBulkEmbedding e slot ∘ (Equiv.refl _).symm)
      else bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)) =
      bulkSlotLeaves n m (movingPatternBulkEmbedding e slot) := by cases b <;> rfl
  rw [he]
  exact (hp.map value).prod_eq

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedCRT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the actual mixed-giant pattern with its corrected CRT mean -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- Each equality class contributes exactly one prime-square factor. -/
theorem movingPatternHaarProduct_eq_image {A B C : Type*} [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → A)
    (P : Finset ℕ) [∀ p : P, Fact p.val.Prime]
    (hP : P = Finset.univ.image (fun c : C => prime (x (e.symm (.inr c)))))
    (hinj : Function.Injective (fun c : C => prime (x (e.symm (.inr c))))) :
    movingPatternHaarProduct e prime hprime n t small bulk pattern x =
      ∏ p : P, movingInternalHaarAverage (fun i => prime (x i))
        (movingPatternFinData e n t small bulk pattern) p.val := by
  let f : C → P := fun c => ⟨prime (x (e.symm (.inr c))), by
    rw [hP]
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact hinj (congrArg Subtype.val hab)
    · intro p
      have hp : p.val ∈ Finset.univ.image (fun c : C => prime (x (e.symm (.inr c)))) := by
        simpa only [hP] using p.property
      obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hp
      exact ⟨c, Subtype.ext hc⟩
  let T := movingPatternFinData e n t small bulk pattern
  let : ∀ c : C, Fact (prime (x (e.symm (.inr c)))).Prime := fun _ => ⟨hprime _⟩
  change (∏ c : C, movingInternalHaarAverage (fun i => prime (x i)) T
    (prime (x (e.symm (.inr c))))) = _
  exact Fintype.prod_equiv (Equiv.ofBijective f hf) _ _ (fun _ => rfl)

section
variable {B C I : Type*} [Fintype C] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (input : PublishedProgressionInput) (Q : ℕ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ)

/-- The original mixed-prime observable, including its internal Haar factors,
is the corrected mean of the separated residue coefficient. -/
theorem movingPatternPrimeObservable_crt (x : Fin (N + 1) → primes)
    (P : Finset ℕ) [∀ q : P, Fact q.val.Prime]
    [∀ b, NeZero (movingArithmeticModuli r p P Finset.univ b)]
    [NeZero (∏ b, movingArithmeticModuli r p P Finset.univ b)]
    (hP : P = Finset.univ.image (fun c : C => (x (e.symm (.inr c)) : ℕ)))
    (hinj : Function.Injective (fun c : C => (x (e.symm (.inr c)) : ℕ)))
    (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
    (hprecision : R ^ (n + 1) ∣ (r : ℤ))
    (hcover : ∀ b, ∀ o ∈ (movingPatternFinBulkData e n m t small slot perm pattern b).occurrences,
      ∀ i ∈ o.current.compensationSlots, (x i : ℕ) ∈ P)
    (hc : Pairwise (fun b c => (movingArithmeticModuli r p P Finset.univ b).Coprime
      (movingArithmeticModuli r p P Finset.univ c)))
    (hpage : pageAtModulus (∏ b, movingArithmeticModuli r p P Finset.univ b)
      (selectedPageZero input Q) = pageAtModulus r (selectedPageZero input Q)) (u v : ℝ) :
    let value := fun i => (x i : ℕ)
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun b => (T b).formulaNodes value
      (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
      (.prime false) (.prime true)
    movingPatternPrimeObservable e t small slot perm pattern primes hprimes childBound pivotBound
      hfreq F E outside R r p g twist input Q v ψ X lo hi hlo hhi φ G (Real.exp u) (Real.exp v) x *
      movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
        n t small (movingPatternBulkLeaves n m slot perm) pattern x =
    movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp u) (Real.exp v) *
      correctedMixedPairAverage input Q (∏ b, movingArithmeticModuli r p P Finset.univ b)
        (movingSeparatedPairResidueCoefficient p value outside F E g (fun b i => twist i b)
          Finset.univ T nodes R) v := by
  dsimp only
  let value := fun i => (x i : ℕ)
  let T := movingPatternFinBulkData e n m t small slot perm pattern
  let hf := movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq
  let nodes := fun b => (T b).formulaNodes value
    (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound (hf b)
    (.prime false) (.prime true)
  have h := movingSeparatedPairResidueCoefficient_page_factorization p value outside F E g
    (fun b i => twist i b) T nodes R r P Finset.univ hf hR hprecision hcover hc input Q hpage v
  have hspec : (∏ i : (Finset.univ : Finset I),
      movingSpectatorHaarAverage value (p i.val) (g i.val) (fun b => twist i.val b) T) =
      ∏ i : I, movingSpectatorHaarAverage value (p i) (g i) (twist i) T := by
    exact Finset.prod_coe_sort Finset.univ
      (fun i => movingSpectatorHaarAverage value (p i) (g i) (twist i) T)
  rw [hspec] at h
  rw [h, movingPatternHaarProduct_eq_image e (fun q : primes => (q : ℕ))
    (fun q => hprimes _ q.property) t small (movingPatternBulkLeaves n m slot perm) pattern x P hP hinj]
  unfold movingPatternPrimeObservable
  let K := movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp u) (Real.exp v)
  let A := movingFrequencyPageAverage value outside F E T nodes R r input Q v
  let S := ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) T
  let H := ∏ q : P, movingInternalHaarAverage value T q.val
  change (K * (A * S)) * H = K * ((A * H) * S)
  ring

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternMixedIntegralCRT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the exact mixed CRT identity with its original outer factors -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype C] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (input : PublishedProgressionInput) (Q : ℕ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ)

/-- Any outer factor can be retained through the finite CRT identity and both
giant integrals. The physical integer measure is `exp(z-center) dz`. -/
theorem movingPatternPrimeObservable_weighted_integral_crt (x : Fin (N + 1) → primes)
    (P : Finset ℕ) [∀ q : P, Fact q.val.Prime]
    [∀ b, NeZero (movingArithmeticModuli r p P Finset.univ b)]
    [NeZero (∏ b, movingArithmeticModuli r p P Finset.univ b)]
    (hP : P = Finset.univ.image (fun c : C => (x (e.symm (.inr c)) : ℕ)))
    (hinj : Function.Injective (fun c : C => (x (e.symm (.inr c)) : ℕ)))
    (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
    (hprecision : R ^ (n + 1) ∣ (r : ℤ))
    (hcover : ∀ b, ∀ o ∈ (movingPatternFinBulkData e n m t small slot perm pattern b).occurrences,
      ∀ i ∈ o.current.compensationSlots, (x i : ℕ) ∈ P)
    (hc : Pairwise (fun b c => (movingArithmeticModuli r p P Finset.univ b).Coprime
      (movingArithmeticModuli r p P Finset.univ c)))
    (hpage : pageAtModulus (∏ b, movingArithmeticModuli r p P Finset.univ b)
      (selectedPageZero input Q) = pageAtModulus r (selectedPageZero input Q))
    (W : ℝ → ℝ → ℂ) (u v a b center : ℝ) :
    let value := fun i => (x i : ℕ)
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun side => (T side).formulaNodes value
      (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq side)
      (.prime false) (.prime true)
    (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      (W z y * movingPatternPrimeObservable e t small slot perm pattern primes hprimes childBound pivotBound
        hfreq F E outside R r p g twist input Q y ψ X lo hi hlo hhi φ G
        (Real.exp z) (Real.exp y) x) * (Real.exp (z - center) : ℂ) / (y : ℂ)) *
      movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
        n t small (movingPatternBulkLeaves n m slot perm) pattern x =
    ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      (W z y * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) *
        correctedMixedPairAverage input Q (∏ j, movingArithmeticModuli r p P Finset.univ j)
          (movingSeparatedPairResidueCoefficient p value outside F E g (fun side i => twist i side)
            Finset.univ T nodes R) y) * (Real.exp (z - center) : ℂ) / (y : ℂ) := by
  dsimp only
  rw [← integral_mul_const]
  congr 1
  funext z
  rw [← integral_mul_const]
  congr 1
  funext y
  have he := movingPatternPrimeObservable_crt e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq F E outside R r p g twist input Q ψ X lo hi hlo hhi φ G
    x P hP hinj hR hprecision hcover hc hpage z y
  dsimp only at he
  calc
    _ = (W z y * (movingPatternPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq F E outside R r p g twist input Q y ψ X lo hi hlo hhi φ G
      (Real.exp z) (Real.exp y) x * movingPatternHaarProduct e (fun q : primes => (q : ℕ))
        (fun q => hprimes _ q.property) n t small (movingPatternBulkLeaves n m slot perm) pattern x)) *
          (Real.exp (z - center) : ℂ) / (y : ℂ) := by ring
    _ = _ := by rw [he]; ring

/-- The ideal diagonal environment is exactly the same CRT integral, with
the two outer cutoffs and remaining inactive regular density retained. -/
theorem movingPatternPrimeObservable_outer_integral_crt (x : Fin (N + 1) → primes)
    (P : Finset ℕ) [∀ q : P, Fact q.val.Prime]
    [∀ b, NeZero (movingArithmeticModuli r p P Finset.univ b)]
    [NeZero (∏ b, movingArithmeticModuli r p P Finset.univ b)]
    (hP : P = Finset.univ.image (fun c : C => (x (e.symm (.inr c)) : ℕ)))
    (hinj : Function.Injective (fun c : C => (x (e.symm (.inr c)) : ℕ)))
    (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
    (hprecision : R ^ (n + 1) ∣ (r : ℤ))
    (hcover : ∀ b, ∀ o ∈ (movingPatternFinBulkData e n m t small slot perm pattern b).occurrences,
      ∀ i ∈ o.current.compensationSlots, (x i : ℕ) ∈ P)
    (hc : Pairwise (fun b c => (movingArithmeticModuli r p P Finset.univ b).Coprime
      (movingArithmeticModuli r p P Finset.univ c)))
    (hpage : pageAtModulus (∏ b, movingArithmeticModuli r p P Finset.univ b)
      (selectedPageZero input Q) = pageAtModulus r (selectedPageZero input Q))
    (density Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ) :
    let value := fun i => (x i : ℕ)
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun side => (T side).formulaNodes value
      (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq side)
      (.prime false) (.prime true)
    (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) * (density : ℂ)) *
        movingPatternPrimeObservable e t small slot perm pattern primes hprimes childBound pivotBound
          hfreq F E outside R r p g twist input Q y ψ X lo hi hlo hhi φ G
          (Real.exp z) (Real.exp y) x) * (Real.exp (z - center) : ℂ) / (y : ℂ)) *
      movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
        n t small (movingPatternBulkLeaves n m slot perm) pattern x =
    ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
      movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
        (Real.exp z) (Real.exp y) * (Real.exp (z - center) : ℂ) *
        ((density : ℂ) * correctedMixedPairAverage input Q
          (∏ j, movingArithmeticModuli r p P Finset.univ j)
          (movingSeparatedPairResidueCoefficient p value outside F E g (fun side i => twist i side)
            Finset.univ T nodes R) y) / (y : ℂ) := by
  dsimp only
  rw [movingPatternPrimeObservable_weighted_integral_crt e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq F E outside R r p g twist input Q ψ X lo hi hlo hhi φ G
    x P hP hinj hR hprecision hcover hc hpage]
  congr 1
  funext z
  congr 1
  funext y
  unfold movingOuterKernel
  ring

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_BulkProgressionCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual frequency/spectator modulus fits one progression cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem bulkProgressionCutoff_bounds (L : ℝ) (hL : 2000 ≤ L) :
    2 ≤ bulkProgressionCutoff L ∧
      Real.log (4 * (bulkProgressionCutoff L : ℝ)) ≤
        2 * Real.exp ((12 / 10000 : ℝ) * L) := by
  have hx : (2 : ℝ) ≤ Real.exp ((12 / 10000 : ℝ) * L) := by
    have hh : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    exact hh.trans (Real.exp_le_exp.mpr (by linarith))
  have hbig : (3 : ℝ) ≤ Real.exp ((12 / 10000 : ℝ) * L) :=
    (by linarith [Real.add_one_le_exp 2] : (3 : ℝ) ≤ Real.exp 2).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hQ : 2 ≤ bulkProgressionCutoff L := by
    apply Nat.le_floor
    exact hx.trans (by linarith [Real.add_one_le_exp (Real.exp ((12 / 10000 : ℝ) * L))])
  refine ⟨hQ, ?_⟩
  have hpos : (0 : ℝ) < bulkProgressionCutoff L := by exact_mod_cast (by omega : 0 < bulkProgressionCutoff L)
  have hf : (bulkProgressionCutoff L : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) :=
    Nat.floor_le (Real.exp_nonneg _)
  have hh := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 4) hpos)
    (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 4))
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hh
  have hlog : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternModulusRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full pattern modulus and the separate giant progression cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem giantProgressionCutoff_bounds (L : ℝ) (hL : 200 ≤ L) :
    2 ≤ giantProgressionCutoff L ∧
      Real.log (4 * (giantProgressionCutoff L : ℝ)) ≤
        2 * Real.exp ((12 / 1000 : ℝ) * L) := by
  have h := bulkProgressionCutoff_bounds (10 * L) (by linarith)
  norm_num [giantProgressionCutoff, ← mul_assoc] at h ⊢
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternGiantBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete logarithmic bounds for the original giant comparison -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem giantProgressionCutoff_log_le {M : ℕ} {L : ℝ}
    (hM : 0 < M) (hbound : M ≤ giantProgressionCutoff L) :
    Real.log (M : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) := by
  have hupper : (M : ℝ) ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
    apply (Nat.cast_le.mpr hbound).trans
    have h := Nat.floor_le (Real.exp_nonneg (Real.exp ((12 / 10000 : ℝ) * (10 * L))))
    simpa only [giantProgressionCutoff, bulkProgressionCutoff,
      show (12 / 10000 : ℝ) * (10 * L) = (12 / 1000 : ℝ) * L by ring] using h
  have hlog := Real.log_le_log (show (0 : ℝ) < M by exact_mod_cast hM) hupper
  simpa only [Real.log_exp] using hlog

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedRegularFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original regular multiplier at the separated arithmetic modulus -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem movingOriginalSupportedSeparatedRegular_modulus_factor {σ I J : Type*} [Fintype J] (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (hcover : ∀ p ∈ outside, ∃ i ∈ S, q i = p)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (Jleft Jright : ℝ) (diagonal : Bool)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (t : Bool → FrequencyTree ℤ n)
    (hT : ∀ side, (T side).Follows (t side)) (hf : ∀ side, (T side).Frequencies (· ≠ 0))
    (hlevels : ∀ side, (T side).Levels tier) (hcoh : ∀ side, (T side).RegularCoherent)
    (hc : ∀ side, (T side).CompensationPrimeData value)
    (hsmall : ∀ side i, (T side).Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ side i, (T side).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (R : ℤ) (hR : ∀ side, (T side).frequencyProduct ∣ R)
    (hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
    (hden : ∀ side i, i ∈ S → (T side).ModularDenominators value (q i))
    (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
    (hregular : ∀ side, MovingSlotReversal.naturalProduct value (T side).regularSlots = ∏ i, reg i)
    (active : J → Bool) (s : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
    (M : ℕ) (hfrequency : R ^ (n + 1) ∣ (M : ℤ))
    (hsquare : ∀ side, ∀ o ∈ (T side).occurrences,
      ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hspectator : ∀ i ∈ S, (q i : ℤ) ∣ M)
    (hregM : ∀ i, reg i ∣ M) (XL XR : ℕ) :
    let nodes := fun side => (T side).formulaNodes value (fun i => (hprime i).ne_zero)
      childBound pivotBound (hf side) (.prime false) (.prime true)
    let c := fun a b => movingSeparatedPairResidueCoefficient q value outside F E g Dq S T nodes R a b *
      (guardedRegularMultiplier reg active s other greg a b : ℂ)
    movingOriginalSupportedOuterPair q value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t XL XR *
        (naturalRegularMultiplier reg active s other greg XL XR : ℂ) =
      if XL.Coprime XR then c (XL % M) (XR % M) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal XL XR else 0 := by
  dsimp only
  let hv := fun i => (hprime i).ne_zero
  let nodes := fun side => (T side).formulaNodes value hv childBound pivotBound (hf side)
    (.prime false) (.prime true)
  let oldM := movingReducedPairModulus value hv outside childBound pivotBound T hf q S
  have he := movingOriginalSupportedOuterPair_reduced_factor q tier value hprime hdisjoint outside
    childBound pivotBound F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD
    hφ hlip hout diagonal T t hT hf hlevels hcoh hc hsmall hfmod (∏ i, reg i) hregular XL XR
  have hback := movingReducedPairResidueCoefficient_modEq q value hv outside childBound pivotBound
    F E g Dq S T hf (XL % oldM) (XR % oldM) XL XR
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XL oldM))
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XR oldM))
  have hsep := movingReducedPairResidueCoefficient_eq_separated q tier value hprime hdisjoint outside
    childBound pivotBound F E g Dq S hcover (fun i _ => hg i) T hlevels hf hsmall hfmod R hR hsmallR
    (fun side => (hc side).distinct) hden XL XR
  have hforward := movingSeparatedPairResidueCoefficient_modEq q value outside F E g Dq S T nodes R hf hR
    XL XR (XL % M) (XR % M) M hfrequency hsquare hspectator
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XL M).symm)
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XR M).symm)
  dsimp only at he hsep
  rw [hback, hsep, hforward] at he
  have hm := multiply_regular_after_support reg active s other greg XL XR _ _ _ he
  have hgmod := guardedRegularMultiplier_modEq reg active s other greg XL XR (XL % M) (XR % M) M
    hregM (Nat.mod_modEq XL M).symm (Nat.mod_modEq XR M).symm
  rw [hgmod] at hm
  exact hm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedDiagonalComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original diagonal giant comparison after integrating the regular primes -/

namespace Ostmann
universe u v w
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_separated_diagonal_haar_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (I : Type v) (J : Type w) [Fintype J]
      (p : I → ℕ) [∀ i, Fact (p i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
      (hprime : ∀ i, (value i).Prime) (_hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
      (outside : List ℕ)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (t : Bool → FrequencyTree ℤ n) (_hT : ∀ b, (T b).Follows (t b))
      (_hlevels : ∀ b, (T b).Levels tier) (_hcoh : ∀ b, (T b).RegularCoherent)
      (_hc : ∀ b, (T b).CompensationPrimeData value)
      (_hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
      (_hfmod : ∀ b i, (T b).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
      (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
      (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
      (g : ∀ i, ZMod (p i) → ℂ) (_hg : ∀ i, g i 0 = 0)
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ) (S : Finset I)
      (R : ℤ) (_hR : ∀ b, (T b).frequencyProduct ∣ R)
      (_hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
      (_hden : ∀ b i, i ∈ S → (T b).ModularDenominators value (p i))
      (_hcover : ∀ q ∈ outside, ∃ i ∈ S, p i = q)
      (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
      (_hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = ∏ i, reg i)
      (active : J → Bool) (sreg : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ M : ℕ, ∀ _hM : NeZero M,
      R ^ (n + 1) ∣ (M : ℤ) →
      (∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ)) →
      (∀ i ∈ S, (p i : ℤ) ∣ (M : ℤ)) →
      (∏ i, reg i).Coprime M →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      ∀ hqeq : q = (∏ i, reg i) * M,
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i ∈ S, (∏ j, reg j).Coprime (p i)) →
      pageAtModulus q (selectedPageZero P Q) =
        pageAtModulus (M) (selectedPageZero P Q) →
      (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
      (∀ i, greg i 0 = 0) → (∀ i, (∑ x : ZMod (reg i), ‖greg i x‖ ^ 2) = reg i) →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c0 := movingSeparatedPairResidueCoefficient p value outside F E g Dq S T nodes R
      let c := fun a b => movingSeparatedPairResidueCoefficient p value outside F E g Dq S T nodes R a b *
        (guardedRegularMultiplier reg active sreg other greg a b : ℂ)
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      let : NeZero q := ⟨by omega⟩
      let : NeZero (M) := ⟨by
        intro hz
        rw [hz, mul_zero] at hqeq
        omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
            Jleft Jright diagonal T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ *
              (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * (((∏ i, if active i then (1 : ℝ) else 1 - (reg i : ℝ)⁻¹ : ℝ) : ℂ) *
              correctedMixedPairAverage P Q (M) c0 y) / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_outer_coprime_mixed_haar_rate n C d] with L hL
  intro σ I J _ p _ tier value hprime hdisjoint outside childBound pivotBound T hf t hT
    hlevels hcoh hc hsmall hfmod F E g hg Dq S R hR hsmallR hden hcover
    reg instReg hregular active sreg other greg ψ X lo hi hlo hhi φ G
    Jleft Jright B D hB hD hφ hlip hout diagonal V hV M hM hfrequency hsquare hspectator hcop
    Q q hQ hq hqQ hqeq houtside hreg hqs hpage hsreg hother hgreg henergy hlog
    u v r s J0 hJ huv hshort hvJ hr hrs hrshort hqlog
  dsimp only
  intro A hA0 hA hbudget
  let : NeZero M := hM
  let : NeZero q := ⟨by omega⟩
  let : ∀ i, NeZero (reg i) := fun i => ⟨(Fact.out : (reg i).Prime).ne_zero⟩
  let : NeZero (∏ i, reg i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (Fact.out : (reg i).Prime).ne_zero)⟩
  let : NeZero ((∏ i, reg i) * M) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
  let c0 := movingSeparatedPairResidueCoefficient p value outside F E g Dq S T nodes R
  let c := fun a b => c0 a b * (guardedRegularMultiplier reg active sreg other greg a b : ℂ)
  have hbase := hL σ value (fun i => (hprime i).ne_zero) childBound pivotBound T hf ψ X lo hi hlo hhi
    φ G Jleft Jright B D hB hD hφ hlip hout diagonal V hV Q q hQ hq hqQ hlog
    u v r s J0 hJ huv hshort hvJ hr hrs hrshort hqlog c A hA0 hA hbudget
  dsimp only at hbase
  have hfactor (x y : ℕ) :
      movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t x y *
          (naturalRegularMultiplier reg active sreg other greg x y : ℂ) =
      if x.Coprime y then c (x % q) (y % q) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal x y else 0 := by
    have hMq : M ∣ q := by rw [hqeq]; exact dvd_mul_left _ _
    exact movingOriginalSupportedSeparatedRegular_modulus_factor p tier value hprime hdisjoint outside
      childBound pivotBound F E g hg Dq S hcover ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      Jleft Jright diagonal T t hT hf hlevels hcoh hc hsmall hfmod R hR hsmallR hden
      reg hregular active sreg other greg q
      (hfrequency.trans (by exact_mod_cast hMq))
      (fun b o ho i hi => (hsquare b o ho i hi).trans (by exact_mod_cast hMq))
      (fun i hi => (hspectator i hi).trans (by exact_mod_cast hMq))
      (fun i => by rw [hqeq]; exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem reg (Finset.mem_univ i)) M) x y
  have hperiod (a b c d : ℕ) (hab : Nat.ModEq M a c) (hbd : Nat.ModEq M b d) : c0 a b = c0 c d := by
    exact movingSeparatedPairResidueCoefficient_modEq p value outside F E g Dq S T nodes R hf hR
      a b c d M hfrequency hsquare hspectator
      (Int.natCast_modEq_iff.mpr hab) (Int.natCast_modEq_iff.mpr hbd)
  have hcrt (y : ℝ) : correctedMixedPairAverage P Q q c y =
      ((∏ i, if active i then (1 : ℝ) else 1 - (reg i : ℝ)⁻¹ : ℝ) : ℂ) *
        correctedMixedPairAverage P Q M c0 y := by
    have hpM : pageAtModulus ((∏ i, reg i) * M) (selectedPageZero P Q) =
        pageAtModulus M (selectedPageZero P Q) := by simpa only [hqeq] using hpage
    have hh := periodic_coefficient_regular_page_average P Q reg hreg M hcop hpM
      active sreg other hsreg hother greg hgreg henergy c0 hperiod y
    simpa only [← hqeq] using hh
  simp_rw [hfactor]
  simpa only [hcrt] using hbase

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise bounds at the separated arithmetic modulus -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSeparatedResidueCoefficient_norm {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode)
    (R x y : ℤ) :
    ‖movingSeparatedResidueCoefficient q value outside F E g D S T nodes R x y‖ ≤
      ‖movingDataWeight F E T‖ * ∏ i ∈ S, B i ^ (2 ^ n) := by
  unfold movingSeparatedResidueCoefficient
  split_ifs
  · rw [norm_mul, norm_prod, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i hi => movingModularSpectator_norm value (q i) (g i) (D i)
        (B i) (hB i hi) (hg i hi) T x y)
  · simp only [norm_zero]
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i hi => pow_nonneg (hB i hi) _)

theorem movingSeparatedPairResidueCoefficient_norm {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (x y : ℕ) :
    ‖movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R x y‖ ≤
      (‖movingDataWeight (F false) (E false) (T false)‖ * ∏ i ∈ S, B i ^ (2 ^ n)) *
      (‖movingDataWeight (F true) (E true) (T true)‖ * ∏ i ∈ S, B i ^ (2 ^ n)) := by
  unfold movingSeparatedPairResidueCoefficient
  rw [norm_mul, Complex.norm_conj]
  apply mul_le_mul
  · exact movingSeparatedResidueCoefficient_norm q value outside _ _ g _ S B hB hg _ _ R x y
  · exact movingSeparatedResidueCoefficient_norm q value outside _ _ g _ S B hB hg _ _ R x y
  · exact norm_nonneg _
  · exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i hi => pow_nonneg (hB i hi) _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RegularMultiplierNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise costs of the actual regular multiplier -/

namespace Ostmann
open scoped Classical BigOperators

theorem guardedRegularMultiplier_le_prime_product {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i) (a b : ℕ) :
    0 ≤ guardedRegularMultiplier p active s other g a b ∧
      guardedRegularMultiplier p active s other g a b ≤ ∏ i, (p i : ℝ) := by
  have hlocal (i) (x : ZMod (p i)) : ‖g i x‖ ^ 2 ≤ (p i : ℝ) := by
    rw [← henergy i]
    exact Finset.single_le_sum (fun y _ => sq_nonneg ‖g i y‖) (Finset.mem_univ x)
  unfold guardedRegularMultiplier naturalRegularMultiplier
  split_ifs
  · constructor
    · exact Finset.prod_nonneg fun i _ => by split <;> positivity
    · apply Finset.prod_le_prod
      · intro i _
        split <;> positivity
      · intro i _
        cases active i <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
        · exact_mod_cast (Fact.out : (p i).Prime).one_le
        · exact hlocal i _
  · exact ⟨le_rfl, Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedRegularNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise norm of the separated coefficient with regular primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSeparatedPair_with_regular_norm {σ I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (reg : J → ℕ) [∀ j, Fact (reg j).Prime]
    (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i z, ‖g i z‖ ≤ p i)
    (Dq : Bool → ∀ i, (ZMod (p i))ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (hweight : ∀ b, ‖movingDataWeight (F b) (E b) (T b)‖ ≤ 1)
    (active : J → Bool) (s : ℤ) (other : ∀ j, ZMod (reg j))
    (greg : ∀ j, ZMod (reg j) → ℂ)
    (henergy : ∀ j, (∑ x : ZMod (reg j), ‖greg j x‖ ^ 2) = reg j) (R : ℤ) (a b : ℕ) :
    ‖movingSeparatedPairResidueCoefficient p value outside F E g Dq Finset.univ T nodes R a b *
      (guardedRegularMultiplier reg active s other greg a b : ℂ)‖ ≤
        (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 * ∏ j, (reg j : ℝ) := by
  have hc := movingSeparatedPairResidueCoefficient_norm p value outside F E g Dq Finset.univ
    (fun i => (p i : ℝ)) (fun i _ => Nat.cast_nonneg _) (fun i _ => hg i) T nodes R a b
  have hr := guardedRegularMultiplier_le_prime_product reg active s other greg henergy a b
  have hprod : 0 ≤ ∏ i, (p i : ℝ) ^ (2 ^ n) := by positivity
  have hcs : ‖movingSeparatedPairResidueCoefficient p value outside F E g Dq Finset.univ T nodes R a b‖ ≤
      (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 := by
    apply hc.trans
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right (hweight false) hprod)
      (mul_le_mul_of_nonneg_right (hweight true) hprod) (by positivity) (by positivity)
    simpa only [one_mul, pow_two] using hh
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.1]
  exact mul_le_mul hcs hr.2 hr.1 (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSeparatedDiagonalRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical giant comparison for the original diagonal -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_separated_diagonal_prime_rate (P : PublishedProgressionInput)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (Afreq Wwin B D : ℝ)
    (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (σ J : Type) [Fintype J] (p : Fin m → ℕ) [∀ i, Fact (p i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
      (hprime : ∀ i, (value i).Prime) (_hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
      (outside : List ℕ)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (t : Bool → FrequencyTree ℤ n) (_hT : ∀ b, (T b).Follows (t b))
      (_hlevels : ∀ b, (T b).Levels tier) (_hcoh : ∀ b, (T b).RegularCoherent)
      (_hc : ∀ b, (T b).CompensationPrimeData value)
      (_hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
      (_hfmod : ∀ b i, (T b).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
      (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
      (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
      (g : ∀ i, ZMod (p i) → ℂ) (_hg : ∀ i, g i 0 = 0)
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ)
      (R : ℤ) (_hR : ∀ b, (T b).frequencyProduct ∣ R)
      (_hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
      (_hden : ∀ b i, (T b).ModularDenominators value (p i))
      (_hcover : ∀ q ∈ outside, ∃ i, p i = q)
      (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
      (_hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = ∏ i, reg i)
      (active : J → Bool) (sreg : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      0 ≤ V → V ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      ∀ M : ℕ, ∀ _hM : NeZero M,
      R ^ (n + 1) ∣ (M : ℤ) →
      (∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ)) →
      (∀ i, (p i : ℤ) ∣ (M : ℤ)) → (∏ i, reg i).Coprime M →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, q ≤ giantProgressionCutoff L →
      ∀ hqeq : q = (∏ i, reg i) * M,
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i, (∏ j, reg j).Coprime (p i)) →
      pageAtModulus q (selectedPageZero P (giantProgressionCutoff L)) =
        pageAtModulus (M) (selectedPageZero P (giantProgressionCutoff L)) →
      (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
      (∀ i, greg i 0 = 0) → (∀ i, (∑ x : ZMod (reg i), ‖greg i x‖ ^ 2) = reg i) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      (∀ b, ‖movingDataWeight (F b) (E b) (T b)‖ ≤ 1) →
      (∀ i z, ‖g i z‖ ≤ p i) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c0 := movingSeparatedPairResidueCoefficient p value outside F E g Dq Finset.univ T nodes R
      let : NeZero q := ⟨by omega⟩
      let : NeZero (M) := ⟨by
        intro hz
        rw [hz, mul_zero] at hqeq
        omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq Finset.univ ψ X lo hi φ G
            Jleft Jright diagonal T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ *
              (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * (((∏ i, if active i then (1 : ℝ) else 1 - (reg i : ℝ)⁻¹ : ℝ) : ℂ) *
              correctedMixedPairAverage P (giantProgressionCutoff L) (M) c0 y) / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  obtain ⟨C, hC, hbudget⟩ := moving_outer_variation_scale ψ n r₀ k Afreq Wwin B D 1
    hAfreq hWwin (by norm_num)
  filter_upwards [P.moving_original_separated_diagonal_haar_rate n C 2,
    eventually_ge_atTop (200 : ℝ)] with L hrate hL
  dsimp only
  intro σ J _ p _ tier value hprime hdisjoint outside childBound pivotBound T hf t hT
    hlevels hcoh hc hsmall hfmod F E g hg Dq R hR hsmallR hden hcover reg _ hregular active sreg other greg
    X lo hi hlo hhi φ G Jleft Jright hφ hlip hout diagonal V hV hV0 hVA hwindow hpupper
    M hM hfrequency hsquare hspectator hcop q hq hqQ hqeq houtside hreg hqs hpage hsreg hother hgreg henergy
    u v r s H hH huv hshort hvH hr hrs hrshort hweight hgnorm
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM.out
  have hregq : (∏ i, reg i) ≤ q := by
    change q = (∏ i, reg i) * M at hqeq
    rw [hqeq]
    exact Nat.le_mul_of_pos_right _ hMpos
  have hqlog := giantProgressionCutoff_log_le (by omega : 0 < q) hqQ
  have hregbound : (∏ i, (reg i : ℝ)) ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
    rw [← Nat.cast_prod]
    apply (Nat.cast_le.mpr hregq).trans
    exact (Real.log_le_iff_le_exp (by exact_mod_cast (show 0 < q by omega))).mp hqlog
  let amp := (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 * ∏ j, (reg j : ℝ)
  have hamp0 : 0 ≤ amp := by dsimp only [amp]; positivity
  have hamp : amp ≤ 4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 *
      Real.exp (1 * L + 1 * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    have hL1 : 1 ≤ L := by linarith only [hL]
    have hcoef : Real.exp ((12 / 1000 : ℝ) * L) ≤
        1 * L + 1 * L * Real.exp ((12 / 1000 : ℝ) * L) := by
      have hh := le_mul_of_one_le_left (Real.exp_nonneg ((12 / 1000 : ℝ) * L)) hL1
      linarith only [hh, hL1]
    have hh := hregbound.trans (Real.exp_le_exp.mpr hcoef)
    apply (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans
    nlinarith only [mul_nonneg (sq_nonneg (∏ i, (p i : ℝ) ^ (2 ^ n)))
      (Real.exp_nonneg (1 * L + 1 * L * Real.exp ((12 / 1000 : ℝ) * L)))]
  have hb := hbudget L (by linarith only [hL]) p V lo hi amp diagonal
    hV0 hVA hhi hwindow hpupper hamp0 hamp
  have hQ := giantProgressionCutoff_bounds L hL
  apply hrate σ (Fin (spectatorBulkCount k L)) J p tier value hprime hdisjoint outside
    childBound pivotBound T hf t hT hlevels hcoh hc hsmall hfmod F E g hg Dq Finset.univ R hR hsmallR
    (fun b i _ => hden b i) (fun q hq => by obtain ⟨i, hi⟩ := hcover q hq; exact ⟨i, Finset.mem_univ i, hi⟩)
    reg hregular active sreg other greg ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD
    hφ hlip hout diagonal V hV M hM hfrequency hsquare
    (fun i _ => hspectator i) hcop (giantProgressionCutoff L) q hQ.1 hq hqQ hqeq houtside
    hreg (fun i _ => hqs i) hpage hsreg hother hgreg henergy hQ.2
    u v r s H hH huv hshort hvH hr hrs hrshort hqlog amp hamp0 _ hb
  intro a ha b hb
  exact movingSeparatedPair_with_regular_norm p reg value outside F E g hgnorm Dq T _
    hweight active sreg other greg henergy R a b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSupportedSeparatedDiagonalRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical giant comparison for the original diagonal -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_supported_separated_diagonal_prime_rate (P : PublishedProgressionInput)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (Afreq Wwin B D : ℝ)
    (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (σ J : Type) [Fintype J] (p : Fin m → ℕ) [∀ i, Fact (p i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
      (hprime : ∀ i, (value i).Prime) (_hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
      (outside : List ℕ)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (t : Bool → FrequencyTree ℤ n) (_hT : ∀ b, (T b).Follows (t b))
      (_hlevels : ∀ b, (T b).Levels tier) (_hcoh : ∀ b, (T b).RegularCoherent)
      (_hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
      (_hfmod : ∀ b i, (T b).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
      (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
      (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
      (g : ∀ i, ZMod (p i) → ℂ) (_hg : ∀ i, g i 0 = 0)
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ)
      (R : ℤ) (_hR : ∀ b, (T b).frequencyProduct ∣ R)
      (_hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
      (_hden : ∀ b i, (T b).ModularDenominators value (p i))
      (_hcover : ∀ q ∈ outside, ∃ i, p i = q)
      (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
      (_hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = ∏ i, reg i)
      (active : J → Bool) (sreg : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      0 ≤ V → V ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      ∀ M : ℕ, ∀ _hM : NeZero M,
      R ^ (n + 1) ∣ (M : ℤ) →
      (∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ)) →
      (∀ i, (p i : ℤ) ∣ (M : ℤ)) → (∏ i, reg i).Coprime M →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, q ≤ giantProgressionCutoff L →
      ∀ hqeq : q = (∏ i, reg i) * M,
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i, (∏ j, reg j).Coprime (p i)) →
      pageAtModulus q (selectedPageZero P (giantProgressionCutoff L)) =
        pageAtModulus (M) (selectedPageZero P (giantProgressionCutoff L)) →
      (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
      (∀ i, greg i 0 = 0) → (∀ i, (∑ x : ZMod (reg i), ‖greg i x‖ ^ 2) = reg i) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      (∀ b, ‖movingDataWeight (F b) (E b) (T b)‖ ≤ 1) →
      (∀ i z, ‖g i z‖ ≤ p i) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c0 := movingSeparatedPairResidueCoefficient p value outside F E g Dq Finset.univ T nodes R
      let : NeZero q := ⟨by omega⟩
      let : NeZero (M) := ⟨by
        intro hz
        rw [hz, mul_zero] at hqeq
        omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq Finset.univ ψ X lo hi φ G
            Jleft Jright diagonal T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ *
              (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * (((∏ i, if active i then (1 : ℝ) else 1 - (reg i : ℝ)⁻¹ : ℝ) : ℂ) *
              correctedMixedPairAverage P (giantProgressionCutoff L) (M) c0 y) / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_original_separated_diagonal_prime_rate ψ n r₀ k Afreq Wwin B D
    hAfreq hWwin hB hD] with L hrate
  dsimp only
  intro σ J _ p _ tier value hprime hdisjoint outside childBound pivotBound T hf t hT
    hlevels hcoh hsmall hfmod F E g hg Dq R hR hsmallR hden hcover reg _ hregular active sreg other greg
    X lo hi hlo hhi φ G Jleft Jright hφ hlip hout diagonal V hV hV0 hVA hwindow hpupper
    M hM hfrequency hsquare hspectator hcop q hq hqQ hqeq houtside hreg hqs hpage hsreg hother hgreg henergy
    u v r s H hH huv hshort hvH hr hrs hrshort hweight hgnorm
  by_cases hd : ∀ b, (T b).CompensationDistinct value
  · have hc : ∀ b, (T b).CompensationPrimeData value := fun b =>
      (T b).compensationPrimeData_of_units value hprime (hsmall b) (hd b)
    exact hrate σ J p tier value hprime hdisjoint outside childBound pivotBound T hf t hT
      hlevels hcoh hc hsmall hfmod F E g hg Dq R hR hsmallR hden hcover reg hregular active sreg other greg
      X lo hi hlo hhi φ G Jleft Jright hφ hlip hout diagonal V hV hV0 hVA hwindow hpupper
      M hM hfrequency hsquare hspectator hcop q hq hqQ hqeq houtside hreg hqs hpage
      hsreg hother hgreg henergy u v r s H hH huv hshort hvH hr hrs hrshort hweight hgnorm
  · obtain ⟨b, hb⟩ := not_forall.mp hd
    have horiginal (XL XR : ℕ) :
        movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq Finset.univ
          ψ X lo hi φ G Jleft Jright diagonal T t XL XR = 0 := by
      have hz := movingSupportedWeight_zero_of_compensation_collision value outside
        (T b) (hcoh b) hb XL XR
      cases b <;> simp only [movingOriginalSupportedOuterPair, hz, map_zero, zero_mul, mul_zero]
    have hsep (nodes : Bool → List MovingFormulaNode) (a b' : ℕ) :
        movingSeparatedPairResidueCoefficient p value outside F E g Dq Finset.univ T nodes R a b' = 0 := by
      have hz := movingSeparatedResidueCoefficient_zero_of_compensation_collision p value outside
        (F b) (E b) g (Dq b) Finset.univ (T b) (nodes b) R a b' (hcoh b) hb
      cases b <;> simp only [movingSeparatedPairResidueCoefficient, hz, map_zero, zero_mul, mul_zero]
    simp [horiginal, hsep, correctedMixedPairAverage, complexPrimeInterval, complexIntegerInterval]
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternDiagonalHaarComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal mixed diagonal comparison for sampled pattern trees -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_pattern_diagonal_haar_rate_oai
    (input : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (Afreq Wwin Bφ Dφ : ℝ) (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C J : Type) [Fintype C] [Fintype J] (N : ℕ)
        (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
        (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ B) (pattern : Bool × MovingSampleIndex n → C)
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) (x : Fin (N + 1) → primes)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
        (reg : J → ℕ) [∀ j, Fact (reg j).Prime]
        (active : J → Bool) (sreg : ℤ) (other : ∀ j, ZMod (reg j))
        (greg : ∀ j, ZMod (reg j) → ℂ)
        (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
        (R : ℤ) (r : ℕ) [NeZero r] (P : Finset ℕ) [∀ q : P, Fact q.val.Prime]
        [∀ b, NeZero (movingArithmeticModuli r p P Finset.univ b)]
        [NeZero (∏ b, movingArithmeticModuli r p P Finset.univ b)]
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (V : ℕ) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ) (diagonal : Bool),
      let value := fun i => (x i : ℕ)
      let T := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
      let M := ∏ b, movingArithmeticModuli r p P Finset.univ b
      let Reg := MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)))
      (∀ b, n ≤ tierB b) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) → value i ≠ value j) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V) → (∀ i, V < value i) →
      (∀ s, ‖f s‖ ≤ 1) → (∀ i, g i 0 = 0) → (∀ i z, ‖g i z‖ ≤ (p i : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      (∀ b, (T b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ i, IsCoprime (value i : ℤ) R) →
      (∀ i j, (value j : ZMod (p i)) ≠ 0) → (∀ i, V < p i) →
      P = Finset.univ.image (fun c : C => value (e.symm (.inr c))) →
      Function.Injective (fun c : C => value (e.symm (.inr c))) →
      Pairwise (fun a b => (movingArithmeticModuli r p P Finset.univ a).Coprime
        (movingArithmeticModuli r p P Finset.univ b)) →
      Reg = ∏ j, reg j → Reg.Coprime M → Reg * M ≤ giantProgressionCutoff L →
      pageAtModulus (Reg * M) (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus M (selectedPageZero input (giantProgressionCutoff L)) →
      pageAtModulus M (selectedPageZero input (giantProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero input (giantProgressionCutoff L)) →
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i, (∏ j, reg j).Coprime (p i)) →
      (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
      (∀ i, greg i 0 = 0) → (∀ i, (∑ z : ZMod (reg i), ‖greg i z‖ ^ 2) = reg i) →
      (V : ℝ) ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ z, |φ z| ≤ Bφ) → (∀ z w, |φ z - φ w| ≤ Dφ * |z - w|) →
      (∀ z, 1 ≤ |z| → φ z = 0) →
      ∀ u v a b center : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → u ≤ v → v ≤ u + 1 → v ≤ center + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ a → a ≤ b → b ≤ a + 1 →
      ‖complexPrimeInterval 1 0 a b (fun y => complexIntegerInterval 1 0 u v center (fun z =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound
            (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g (fun _ => Dq) Finset.univ
            ψ X lo hi φ G Jleft Jright diagonal T t ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ *
          (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
        (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
          ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
            (((∏ j, if active j then (1 : ℝ) else 1 - (reg j : ℝ)⁻¹) : ℝ) : ℂ)) *
            movingPatternPrimeObservable e t (fun _ => small) slot (Equiv.refl _) pattern
              primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
              (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input
              (giantProgressionCutoff L) y ψ X lo hi hlo hhi φ G (Real.exp z) (Real.exp y) x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)) *
          movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
            n t (fun _ => small) (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
          Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [input.moving_original_supported_separated_diagonal_prime_rate ψ n r₀ k
    Afreq Wwin Bφ Dφ hAfreq hWwin hBφ hDφ] with L hL
  dsimp only
  intro B C J _ _ N e tierB tierC t small slot pattern primes hprimes x p _ g Dq
    reg _ active sreg other greg f outside childBound pivotBound R r _ P _ _ _ hfreq V
    X lo hi hlo hhi φ G Jleft Jright diagonal
  let m := spectatorBulkCount k L
  let value := fun i => (x i : ℕ)
  let T := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
  let hf := movingPatternFinBulkData_frequencies e t (fun _ => small) slot (Equiv.refl _)
    pattern (· ≠ 0) hfreq
  let nodes := fun b => (T b).formulaNodes value (fun i => (hprimes _ (x i).property).ne_zero)
    childBound pivotBound (hf b) (.prime false) (.prime true)
  let M := ∏ b, movingArithmeticModuli r p P Finset.univ b
  intro hB htier hdisjoint hV hlarge hfnorm hg hgnorm hout hR hprecision hsmallR hres hspecLarge hP hinj hc
    hRegEq hcop hfull hpageReg hpage houtside hreg hqs hsreg hother hgreg henergy
    hVA hwindow hpupper hφ hlip hφout u v a b center hcenter huv hv hvcenter ha hab hb
  have hprime (i) : (value i).Prime := hprimes _ (x i).property
  have hVN (side) : (T side).Frequencies (fun s => s.natAbs ≤ V) :=
    movingPatternFinBulkData_frequencies e t (fun _ => small) slot (Equiv.refl _) pattern _ hV side
  have hVR (side) : (T side).Frequencies (fun s => |(s : ℝ)| ≤ (V : ℝ)) :=
    (hVN side).mono (fun s hs => by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (show (s.natAbs : ℝ) ≤ V by exact_mod_cast hs))
  have hsmall (side) := (T side).small_frequency_units value hprime V hlarge (hf side) (hVN side)
  have hfmod (side) := (T side).small_frequency_residues value hprime V hlarge (hf side) (hVN side)
  have hden (side i) : (T side).ModularDenominators value (p i) := by
    apply (T side).modularDenominators_of_units value (p i) (hres i)
    exact movingPatternFinBulkData_frequencies e t (fun _ => small) slot (Equiv.refl _)
      pattern (fun s => (s : ZMod (p i)) ≠ 0)
      (fun b s hs => intCast_ne_zero_of_natAbs_lt (p i) s (hfreq b s hs)
        ((hV b s hs).trans_lt (hspecLarge i))) side
  have hcover := movingPatternFinBulkData_internal_cover e tierB tierC t (fun _ => small)
    slot (Equiv.refl _) pattern hB htier (fun q : primes => (q : ℕ)) x
  have hcoverP (side o) (ho : o ∈ (T side).occurrences) (j) (hj : j ∈ o.current.compensationSlots) :
      value j ∈ P := by
    rw [hP]
    exact hcover side o ho j hj
  have hperiod := movingArithmeticModuli_periods r p P Finset.univ R (n + 1) hprecision

  have hweight (side) : ‖movingDataWeight (fun {_} _ => f) (fun {_} _ _ _ _ => 1) (T side)‖ ≤ 1 :=
    movingDataWeight_unit_norm_le_one (fun {_} _ => f) (fun s _ => hfnorm s) (T side)
  have hregular (side) : MovingSlotReversal.naturalProduct value (T side).regularSlots = ∏ j, reg j :=
    (movingPatternFinBulkData_regular_product e t small slot pattern value side).trans hRegEq
  have hqpos : 1 ≤ (∏ j, reg j) * M := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => (Fact.out : (reg j).Prime).ne_zero))
      (NeZero.ne M)
  have hh := hL (Fin (N + 1)) J p ((Sum.elim tierB tierC) ∘ e) value hprime hdisjoint outside
    childBound pivotBound T hf t
    (movingPatternFinBulkData_follows e t (fun _ => small) slot (Equiv.refl _) pattern)
    (movingPatternFinBulkData_levels e tierB tierC n m t (fun _ => small) slot (Equiv.refl _) pattern hB htier)
    (movingPatternFinBulkData_regular_coherent e t (fun _ => small) slot (Equiv.refl _) pattern)
    hsmall hfmod (fun _ {_} _ => f) (fun _ {_} _ _ _ _ => 1) g hg (fun _ => Dq)
    R hR hsmallR (fun side i => hden side i) hout reg hregular active sreg other greg
    X lo hi hlo hhi φ G Jleft Jright hφ hlip hφout diagonal V hVR (Nat.cast_nonneg _) hVA hwindow hpupper
    M inferInstance hperiod.1 (fun side o ho j hj => hperiod.2.1 _ (hcoverP side o ho j hj))
    (fun i => hperiod.2.2 i (Finset.mem_univ i))
    (by simpa only [hRegEq] using hcop)
    ((∏ j, reg j) * M) hqpos (by simpa only [hRegEq] using hfull) rfl
    houtside hreg hqs (by simpa only [hRegEq] using hpageReg)
    hsreg hother hgreg henergy u v a b center hcenter huv hv hvcenter ha hab hb hweight hgnorm
  rw [movingPatternPrimeObservable_outer_integral_crt e t (fun _ => small) slot (Equiv.refl _)
    pattern primes hprimes childBound pivotBound hfreq (fun _ {_} _ => f)
    (fun _ {_} _ _ _ _ => 1) outside R r p g (fun i _ => Dq i) input (giantProgressionCutoff L)
    ψ X lo hi hlo hhi φ G x P hP hinj hR hprecision hcoverP hc hpage]
  exact hh

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.moving_pattern_diagonal_haar_rate_oai := @OAI.Ostmann.PublishedProgressionInput.moving_pattern_diagonal_haar_rate_oai
