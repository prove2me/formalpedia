-- Prove2me | solution 1 for OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:58:48.190532+00:00
-- url     : https://prove2.me/submissions/e2a4e172-4761-476b-8660-3b3b3ebfedbe

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D006
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_sparse_finite_contraction

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarePullback
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The factor two in square pullbacks

The finite-fiber bound and Cauchy--Schwarz estimate used in the manuscript's
equation `tree-square-pullback`. Multiplicative characters are extended by zero
at zero, as in the manuscript. Evaluations in these lemmas are at units.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.instDecidableEqMulCharZModComplex_solutions
/-- A multiplicative character has modulus one at each unit. -/
theorem norm_mulChar_unit {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (u : (ZMod p)ˣ) : ‖χ u‖ = 1 := by
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

theorem additiveFourier_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => c * f x) a = c * additiveFourier f a := by
  simp only [additiveFourier_apply, mul_assoc]
  rw [← Finset.mul_sum]
  ring

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
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourierBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two local Fourier bounds in the large-kernel correlation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_twice {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : ZMod q) :
    additiveFourier (additiveFourier f) a = (q : ℂ)⁻¹ * f (-a) := by
  rw [additiveFourier_apply]
  congr 1
  have hi := additiveFourier_inversion f (-a)
  simpa only [mul_neg] using hi.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_Mellin
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mellin coefficients of a square pullback

Character orthogonality identifies the coefficient after substituting
`K * z^2`. The factor-two estimate then follows from `SquarePullback`.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.instDecidableEqMulCharZModComplex_solutions_1
theorem sum_mulChar_units_eq_zero {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    (∑ z : (ZMod p)ˣ, χ z) = 0 := by
  obtain ⟨b, hb⟩ := MulChar.ne_one_iff.mp hχ
  apply eq_zero_of_mul_eq_self_left hb
  calc
    χ b * ∑ z : (ZMod p)ˣ, χ z = ∑ z : (ZMod p)ˣ, χ (b * z) := by
      simp only [Finset.mul_sum, map_mul]
    _ = ∑ z : (ZMod p)ˣ, χ z :=
      (Equiv.mulLeft b).bijective.sum_comp (fun z : (ZMod p)ˣ => χ z)

theorem sum_mulChar_units_eq_ite {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) :
    (∑ z : (ZMod p)ˣ, χ z) =
      if χ = 1 then (Fintype.card (ZMod p)ˣ : ℂ) else 0 := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    simp only [MulChar.one_apply_coe, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, ite_true, if_true]
  · simp only [hχ, ite_false, if_false, sum_mulChar_units_eq_zero χ hχ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MellinParseval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mellin inversion and Parseval on the nonzero residues

The coefficients use the probability normalization from `Mellin.lean`.
The only character-theoretic input is the finite duality already in Mathlib.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.instFintypeMulCharZModComplexOfFactPrime_solutions
noncomputable local instance instDecidableEqMulCharZModComplex_solutions_2_r209b90_1 {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) :=
  Classical.decEq _
/-- There are exactly as many complex multiplicative characters as units. -/
theorem card_mulChar_eq_card_units {p : ℕ} [Fact p.Prime] :
    Fintype.card (MulChar (ZMod p) ℂ) = Fintype.card (ZMod p)ˣ := by
  simpa only [Nat.card_eq_fintype_card] using
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity (ZMod p) ℂ

/-- Summing characters detects the identity element. -/
theorem sum_mulChar_apply_eq_ite {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    (∑ χ : MulChar (ZMod p) ℂ, χ u) =
      if u = 1 then (Fintype.card (ZMod p)ˣ : ℂ) else 0 := by
  classical
  by_cases hu : u = 1
  · subst u
    simp only [Units.val_one, map_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ite_true, if_true, card_mulChar_eq_card_units]
  · simp only [hu, ite_false, if_false]
    have huval : (u : ZMod p) ≠ 1 := by
      intro h
      exact hu (Units.ext h)
    obtain ⟨χ₀, hχ₀⟩ :=
      MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod p) ℂ huval
    apply eq_zero_of_mul_eq_self_left hχ₀
    calc
      χ₀ u * ∑ χ : MulChar (ZMod p) ℂ, χ u =
          ∑ χ : MulChar (ZMod p) ℂ, (χ₀ * χ) u := by
        simp only [Finset.mul_sum, MulChar.coeToFun_mul, Pi.mul_apply]
      _ = ∑ χ : MulChar (ZMod p) ℂ, χ u :=
        (Equiv.mulLeft χ₀).bijective.sum_comp (fun χ : MulChar (ZMod p) ℂ => χ u)

/-- The dual orthogonality identity, with the sum over characters. -/
theorem mellin_dual_orthogonality {p : ℕ} [Fact p.Prime] (x z : (ZMod p)ˣ) :
    (∑ χ : MulChar (ZMod p) ℂ, χ x * conj (χ z)) =
      if x = z then (Fintype.card (ZMod p)ˣ : ℂ) else 0 := by
  have hterm : ∀ χ : MulChar (ZMod p) ℂ,
      χ x * conj (χ z) = χ ((x / z : (ZMod p)ˣ) : ZMod p) := by
    intro χ
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, map_mul,
      ← MulChar.inv_apply', MulChar.inv_apply_eq_inv',
      Complex.inv_eq_conj (norm_mulChar_unit χ z)]
  simp_rw [hterm]
  rw [sum_mulChar_apply_eq_ite]
  simp only [div_eq_one]

/-- Full finite Mellin inversion for arbitrary complex functions on the units. -/
theorem mellin_inversion {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)ˣ → ℂ) (x : (ZMod p)ˣ) :
    (∑ χ : MulChar (ZMod p) ℂ, mellinCoefficient f χ * χ x) = f x := by
  classical
  have hc : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold mellinCoefficient
  calc
    (∑ χ : MulChar (ZMod p) ℂ,
        ((Fintype.card (ZMod p)ˣ : ℂ)⁻¹ * ∑ z, f z * conj (χ z)) * χ x) =
        (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ *
          ∑ z : (ZMod p)ˣ, f z * ∑ χ : MulChar (ZMod p) ℂ, χ x * conj (χ z) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = f x := by
      simp_rw [mellin_dual_orthogonality]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
      field_simp

/-- The exact probability-normalized Parseval identity. -/
theorem mellin_parseval {p : ℕ} [Fact p.Prime] (f : (ZMod p)ˣ → ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ‖mellinCoefficient f χ‖ ^ 2) =
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ z : (ZMod p)ˣ, ‖f z‖ ^ 2 := by
  have hcomplex :
      (∑ χ : MulChar (ZMod p) ℂ, conj (mellinCoefficient f χ) * mellinCoefficient f χ) =
        (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ *
          ∑ z : (ZMod p)ˣ, conj (f z) * f z := by
    calc
      _ = ∑ χ : MulChar (ZMod p) ℂ, conj (mellinCoefficient f χ) *
          ((Fintype.card (ZMod p)ˣ : ℂ)⁻¹ * ∑ z : (ZMod p)ˣ, f z * conj (χ z)) := rfl
      _ = (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ * ∑ z : (ZMod p)ˣ,
          (∑ χ : MulChar (ZMod p) ℂ, conj (mellinCoefficient f χ) * conj (χ z)) * f z := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by
        have hsum : ∀ z : (ZMod p)ˣ,
            (∑ χ : MulChar (ZMod p) ℂ, conj (mellinCoefficient f χ) * conj (χ z)) =
              conj (f z) := by
          intro z
          calc
            _ = ∑ χ : MulChar (ZMod p) ℂ,
                conj (mellinCoefficient f χ * χ z) := by simp only [map_mul]
            _ = conj (∑ χ : MulChar (ZMod p) ℂ,
                mellinCoefficient f χ * χ z) := (map_sum (starRingEnd ℂ) _ _).symm
            _ = conj (f z) := congrArg conj (mellin_inversion f z)
        simp_rw [hsum]
  simp_rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_sum] at hcomplex
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.ofReal_sum, Complex.ofReal_pow] using hcomplex

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_GaussFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Additive Fourier coefficients of multiplicative characters

The Gauss identity already proved in Mathlib gives the exact normalized
squared modulus needed for the two-bad quartet estimate in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The Fourier transform exchanges pointwise multiplication and convolution. -/
theorem additiveFourier_pointwise_mul {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => f x * g x) a =
      ∑ b : ZMod p, additiveFourier f b * additiveFourier g (a - b) := by
  rw [additiveFourier_apply]
  conv_lhs =>
    enter [2, 2, x]
    rw [additiveFourier_inversion f x]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [additiveFourier_apply g (a - b)]
  simp only [Finset.mul_sum]
  have hphase (x : ZMod p) :
      ZMod.stdAddChar (b * x) * ZMod.stdAddChar (-(x * a)) =
        ZMod.stdAddChar (-(x * (a - b))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = (p : ℂ)⁻¹ * additiveFourier f b * g x *
        (ZMod.stdAddChar (b * x) * ZMod.stdAddChar (-(x * a))) := by ring
    _ = _ := by rw [hphase]; ring

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

theorem normalizedResidueIndicator_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, normalizedResidueIndicator S x) = 0 := by
  simp only [normalizedResidueIndicator, ← Complex.ofReal_sum, ← Finset.sum_div,
    centeredDensity_sum, zero_div, Complex.ofReal_zero]

theorem normalizedResidueIndicator_energy {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hS : S.Nonempty) (hSp : S.card < p) :
    (∑ x : ZMod p, ‖normalizedResidueIndicator S x‖ ^ 2) = p := by
  have hv := residueVariance_pos S hS hSp
  simp only [normalizedResidueIndicator, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    div_pow, ← Finset.sum_div, Real.sq_sqrt hv.le, centeredDensity_sq_sum]
  exact mul_div_cancel_right₀ (p : ℝ) hv.ne'

theorem normalizedResidueTransform_zero {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    normalizedResidueTransform S 0 = 0 := by
  simp only [normalizedResidueTransform, densityFourier, additiveFourier_apply,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, normalizedResidueIndicator_sum]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothPrimeMeanTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed smooth test for the prime mean of the sparse weight -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem primeMeanTest_compactSupport : HasCompactSupport primeMeanTest :=
  HasCompactSupport.intro isCompact_Icc primeMeanTest_zero_outside

theorem primeMeanTest_center : primeMeanTest (3 / 4) = 1 := by
  norm_num [primeMeanTest, logCellProfile, Real.smoothTransition.zero,
    Real.smoothTransition.one]

theorem primeMeanTest_integral_pos : 0 < ∫ t : ℝ, primeMeanTest t := by
  apply (primeMeanTest_contDiff (n := 0)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := (3 / 4 : ℝ)) primeMeanTest_compactSupport primeMeanTest_nonneg
  rw [primeMeanTest_center]
  norm_num

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothPrimePowerRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing higher prime powers from the fixed smooth mean -/
namespace Ostmann
open scoped Classical BigOperators

 theorem primeMeanTest_nat_support (X : ℝ) (hX : 0 < X) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 ⌊X⌋₊) : primeMeanTest (n / X) = 0 := by
  apply primeMeanTest_zero_outside
  intro h
  apply hn
  rw [Finset.mem_Ioc]
  constructor
  · by_contra hz
    have : n = 0 := by omega
    subst n
    norm_num at h
  · apply (Nat.le_floor_iff hX.le).mpr
    have hh := (div_le_iff₀ hX).mp h.2
    linarith

 theorem smoothMangoldtMean_eq_sum (q : ℕ) (χ : DirichletCharacter ℂ q)
    (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean q χ X = ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * primeMeanTest (n / X) := by
  apply tsum_eq_sum
  intro n hn
  rw [primeMeanTest_nat_support X hX n hn, Complex.ofReal_zero, mul_zero]

 theorem smooth_mangoldt_prime_error (g : ℕ → ℂ) (X B : ℝ)
    (hX : 1 ≤ X) (hB : 0 ≤ B)
    (hg : ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊, ‖g n‖ ≤ B) :
    ‖(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X)) -
      smoothPrimeSum g X‖ ≤ B * (2 * Real.sqrt X * Real.log X) := by
  have he : (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X)) -
      smoothPrimeSum g X =
      ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X) := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊X⌋₊) Nat.Prime
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X))
    have hp : (∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
        (ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X)) =
        smoothPrimeSum g X := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
    rw [hp] at h
    exact (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)).symm
  rw [he]
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * g n * primeMeanTest (n / X)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        B * ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        abs_of_nonneg (primeMeanTest_nonneg _)]
      calc
        _ ≤ ArithmeticFunction.vonMangoldt n * B * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hg n (Finset.mem_filter.mp hn).1)
            ArithmeticFunction.vonMangoldt_nonneg) (primeMeanTest_le_one _)
            (primeMeanTest_nonneg _) (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hB)
        _ = _ := by ring
    _ = B * (Chebyshev.psi X - Chebyshev.theta X) := by
      rw [← Finset.mul_sum, nonprime_mangoldt_sum]
    _ ≤ B * (2 * Real.sqrt X * Real.log X) :=
      mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hX)) hB

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPrimeMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-power removal for a finite primitive character expansion -/
namespace Ostmann
open scoped Classical BigOperators

 theorem principal_modulus_one_apply (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
  have hn : IsUnit (n : ZMod 1) := by
    rw [Subsingleton.elim (n : ZMod 1) 1]
    exact isUnit_one
  exact MulChar.one_apply hn

 theorem primitiveCharacterPolynomial_norm (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (B : ℝ)
    (hc₀ : ‖c₀‖ ≤ B) (hc : ∀ ρ ∈ F, ‖c ρ‖ ≤ B) (a : ℕ) :
    ‖primitiveCharacterPolynomial F c c₀ a‖ ≤ B * (1 + F.card) := by
  calc
    _ ≤ ‖c₀‖ + ∑ ρ ∈ F, ‖c ρ * ρ.character (a : ZMod ρ.modulus)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ B + ∑ _ρ ∈ F, B := by
      apply add_le_add hc₀
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (ρ.character.norm_le_one _)).trans (hc ρ hρ)
    _ = _ := by simp; ring

 theorem character_smooth_mean_identity (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (X : ℝ) (hX : 0 < X) :
    c₀ * smoothMangoldtMean 1 1 X +
      ∑ ρ ∈ F, c ρ * smoothMangoldtMean ρ.modulus ρ.character X =
      ∑ a ∈ Finset.Ioc 0 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt a : ℂ) *
        primitiveCharacterPolynomial F c c₀ a * primeMeanTest (a / X) := by
  simp_rw [smoothMangoldtMean_eq_sum _ _ X hX, principal_modulus_one_apply, mul_one]
  unfold primitiveCharacterPolynomial
  simp_rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    ring
  · apply Finset.sum_congr rfl
    intro ρ hρ
    apply Finset.sum_congr rfl
    intro a ha
    ring

 theorem character_prime_power_error (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (X B : ℝ) (hX : 1 ≤ X)
    (hB : 0 ≤ B) (hc₀ : ‖c₀‖ ≤ B) (hc : ∀ ρ ∈ F, ‖c ρ‖ ≤ B) :
    ‖c₀ * smoothMangoldtMean 1 1 X +
      ∑ ρ ∈ F, c ρ * smoothMangoldtMean ρ.modulus ρ.character X -
      smoothPrimeSum (primitiveCharacterPolynomial F c c₀) X‖ ≤
      (B * (1 + F.card)) * (2 * Real.sqrt X * Real.log X) := by
  rw [character_smooth_mean_identity F c c₀ X (by linarith)]
  exact smooth_mangoldt_prime_error _ X _ hX (by positivity)
    (fun a _ => primitiveCharacterPolynomial_norm F c c₀ B hc₀ hc a)

 theorem character_prime_power_error_of_conductor (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (X B : ℝ) (hX : 1 ≤ X)
    (hB : 0 ≤ B) (hc₀ : ‖c₀‖ ≤ B) (hc : ∀ ρ ∈ F, ‖c ρ‖ ≤ B)
    (Q : ℕ) (hQ : ∀ ρ ∈ F, ρ.modulus ≤ Q) :
    ‖c₀ * smoothMangoldtMean 1 1 X +
      ∑ ρ ∈ F, c ρ * smoothMangoldtMean ρ.modulus ρ.character X -
      smoothPrimeSum (primitiveCharacterPolynomial F c c₀) X‖ ≤
      (B * (1 + (Q : ℝ) ^ 2)) * (2 * Real.sqrt X * Real.log X) := by
  apply (character_prime_power_error F c c₀ X B hX hB hc₀ hc).trans
  have hcard : (F.card : ℝ) ≤ (Q : ℝ) ^ 2 := by
    exact_mod_cast primitive_character_family_card F Q hQ
  gcongr
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.log_nonneg hX)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteCauchyEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient bounds by finite Fourier inversion on a circle

For a finite polynomial, a sufficiently large root-of-unity grid recovers every
coefficient exactly. This supplies the Cauchy estimate used in Section 5.3,
including for finite-dimensional operator spaces, without a dimension factor.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem cyclicPolynomial_eq_invDFT {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E] (c : ZMod N → E) (r : ℝ) :
    cyclicPolynomial c r = (N : ℂ) •
      ZMod.dft.symm (fun j => ((r ^ j.val : ℝ) : ℂ) • c j) := by
  funext z
  simp only [Pi.smul_apply, ZMod.invDFT_apply, smul_smul, mul_inv_cancel₀ (NeZero.ne (N : ℂ)),
    one_smul, cyclicPolynomial]

theorem cyclicPolynomial_coefficient {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E] (c : ZMod N → E) (r : ℝ) (j : ZMod N) :
    (N : ℂ)⁻¹ • ZMod.dft (cyclicPolynomial c r) j = ((r ^ j.val : ℝ) : ℂ) • c j := by
  rw [cyclicPolynomial_eq_invDFT, map_smul]
  simp only [LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_smul,
    ← mul_assoc, inv_mul_cancel₀ (NeZero.ne (N : ℂ)), one_mul]

theorem normalized_dft_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ZMod N → E) (M : ℝ) (hM : ∀ z, ‖f z‖ ≤ M) (j : ZMod N) :
    ‖(N : ℂ)⁻¹ • ZMod.dft f j‖ ≤ M := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hd : ‖ZMod.dft f j‖ ≤ N * M := by
    rw [ZMod.dft_apply]
    calc
      _ ≤ ∑ z, ‖ZMod.stdAddChar (-(z * j)) • f z‖ := norm_sum_le _ _
      _ = ∑ z, ‖f z‖ := by simp only [norm_smul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
      _ ≤ ∑ _z : ZMod N, M := Finset.sum_le_sum (fun z _ => hM z)
      _ = _ := by simp
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (N : ℝ)⁻¹ * (N * M) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = M := by rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

theorem cyclicPolynomial_coefficient_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ZMod N → E) (r M : ℝ) (hr : 0 < r)
    (hM : ∀ z, ‖cyclicPolynomial c r z‖ ≤ M) (j : ZMod N) :
    ‖c j‖ ≤ M / r ^ j.val := by
  have hh := normalized_dft_norm_le (cyclicPolynomial c r) M hM j
  rw [cyclicPolynomial_coefficient, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (pow_pos hr _)] at hh
  exact (le_div_iff₀ (pow_pos hr _)).mpr (by simpa only [mul_comm] using hh)

theorem cyclicPolynomial_two_coefficient_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ZMod N → ZMod N → E) (r M : ℝ) (hr : 0 < r)
    (hM : ∀ z w, ‖cyclicPolynomial (fun i => cyclicPolynomial (c i) r w) r z‖ ≤ M)
    (i j : ZMod N) : ‖c i j‖ ≤ M / r ^ i.val / r ^ j.val := by
  apply cyclicPolynomial_coefficient_norm_le (c i) r (M / r ^ i.val) hr
  intro w
  exact cyclicPolynomial_coefficient_norm_le
    (fun i => cyclicPolynomial (c i) r w) r M hr (fun z => hM z w) i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialCircleEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cauchy and truncation estimates for ordinary finite polynomials -/

namespace Ostmann
open scoped Classical BigOperators

theorem sum_zmod_val {N : ℕ} [NeZero N] {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) : (∑ j : ZMod N, f j.val) = ∑ j ∈ Finset.range N, f j := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact Fin.sum_univ_eq_sum_range f (n + 1)

theorem cyclicPolynomial_eq_finitePolynomial {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E] (c : ℕ → E) (r : ℝ) (z : ZMod N) :
    cyclicPolynomial (fun i : ZMod N => c i.val) r z =
      finitePolynomial c N ((r : ℂ) * ZMod.stdAddChar z) := by
  have hc (i : ZMod N) : ZMod.stdAddChar (i * z) = ZMod.stdAddChar z ^ i.val := by
    calc
      _ = ZMod.stdAddChar ((i.val : ZMod N) * z) := by rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  unfold cyclicPolynomial finitePolynomial
  calc
    _ = ∑ i : ZMod N, (((r : ℂ) * ZMod.stdAddChar z) ^ i.val) • c i.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc, smul_smul, mul_pow, Complex.ofReal_pow, mul_comm]
    _ = _ := sum_zmod_val (N := N) (fun i => (((r : ℂ) * ZMod.stdAddChar z) ^ i) • c i)

theorem finitePolynomial₂_coefficient_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℕ → ℕ → E) (r M : ℝ) (hr : 0 < r)
    (hM : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r → ‖finitePolynomial₂ c N u v‖ ≤ M)
    (i j : ℕ) (hi : i < N) (hj : j < N) :
    ‖c i j‖ ≤ M / r ^ i / r ^ j := by
  have hn (z : ZMod N) : ‖(r : ℂ) * ZMod.stdAddChar z‖ = r := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
  have hgrid (z w : ZMod N) :
      ‖cyclicPolynomial (fun i : ZMod N =>
        cyclicPolynomial (fun j : ZMod N => c i.val j.val) r w) r z‖ ≤ M := by
    simp_rw [cyclicPolynomial_eq_finitePolynomial]
    rw [cyclicPolynomial_eq_finitePolynomial
      (fun i => finitePolynomial (c i) N ((r : ℂ) * ZMod.stdAddChar w)) r z]
    exact hM _ _ (hn z) (hn w)
  have hh := cyclicPolynomial_two_coefficient_norm_le
    (fun i j : ZMod N => c i.val j.val) r M hr hgrid (i : ZMod N) (j : ZMod N)
  simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hh

theorem finitePolynomial₂_coefficient_unique {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c d : ℕ → ℕ → E)
    (h : ∀ u v, finitePolynomial₂ c N u v = finitePolynomial₂ d N u v)
    (i j : ℕ) (hi : i < N) (hj : j < N) : c i j = d i j := by
  have hz (u v : ℂ) : finitePolynomial₂ (fun i j => c i j - d i j) N u v = 0 := by
    simp only [finitePolynomial₂, finitePolynomial, smul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (h u v)
  have hc := finitePolynomial₂_coefficient_norm_le (fun i j => c i j - d i j)
    1 0 (by norm_num) (by intro u v _ _; rw [hz]; simp) i j hi hj
  have he : c i j - d i j = 0 := norm_le_zero_iff.mp (by simpa using hc)
  exact sub_eq_zero.mp he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveCharacterReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduction to the actual primitive character, without multiplicities

At a fixed ambient modulus, passage to primitive characters is injective.
Thus grouping the sparse expansion introduces no coefficient multiplicity.
-/
namespace Ostmann
open scoped Classical

theorem primitiveCharacterReduction_injective (N : ℕ) [NeZero N] :
    Function.Injective (primitiveCharacterReduction (N := N)) := by
  intro χ ψ h
  have he := congrArg (liftPrimitiveCharacter N) h
  simpa only [lift_primitiveCharacterReduction] using he

theorem primitiveCharacterReduction_modulus_le {N d : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hd : χ.FactorsThrough d)
    (ρ : PrimitiveComplexCharacter) (hρ : primitiveCharacterReduction χ = some ρ) :
    ρ.modulus ≤ d := by
  rw [primitiveCharacterReduction_modulus χ ρ hρ]
  apply Nat.le_of_dvd
  · have hd0 : d ≠ 0 := by
      intro h
      have hh := hd.dvd
      rw [h] at hh
      exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hh)
    exact Nat.pos_of_ne_zero hd0
  · exact χ.conductor_dvd_of_mem_conductorSet hd

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTransformSpectrum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration of a small-L1 normalized additive transform

This is the finite argument (5.7), before the contracting kernel in
Proposition 5.1. It requires no analytic input.
-/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem largeTransformSpectrum_zero_not_mem {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : g 0 = 0) : 0 ∉ largeTransformSpectrum g := by
  simp [largeTransformSpectrum, hg]

theorem largeTransformSpectrum_neg {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : ∀ b, g (-b) = conj (g b)) (b : ZMod p) :
    -b ∈ largeTransformSpectrum g ↔ b ∈ largeTransformSpectrum g := by
  simp only [largeTransformSpectrum, Finset.mem_filter, Finset.mem_univ, true_and,
    hg, Complex.norm_conj]

/-- The large coefficients occupy a small set and retain almost all energy. -/
theorem largeTransformSpectrum_bounds {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (δ : ℝ)
    (hL1 : (∑ b, ‖g b‖) ≤ δ * p) (hL2 : (∑ b, ‖g b‖ ^ 2) = p) :
    ((largeTransformSpectrum g).card : ℝ) ≤ δ * p ∧
      (1 - δ) * p ≤ ∑ b ∈ largeTransformSpectrum g, ‖g b‖ ^ 2 := by
  let E := largeTransformSpectrum g
  have hcard : (E.card : ℝ) ≤ ∑ b ∈ E, ‖g b‖ := by
    calc
      _ = ∑ _b ∈ E, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun b hb =>
        (Finset.mem_filter.mp hb).2.le
  have hL1E : (∑ b ∈ E, ‖g b‖) ≤ ∑ b, ‖g b‖ :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
  refine ⟨hcard.trans (hL1E.trans hL1), ?_⟩
  have hsmall : (∑ b ∈ Finset.univ \ E, ‖g b‖ ^ 2) ≤ δ * p := by
    calc
      _ ≤ ∑ b ∈ Finset.univ \ E, ‖g b‖ := by
        apply Finset.sum_le_sum
        intro b hb
        have hn : ‖g b‖ ≤ 1 := by
          have hnot := (Finset.mem_sdiff.mp hb).2
          simpa only [E, largeTransformSpectrum, Finset.mem_filter, Finset.mem_univ,
            true_and, not_lt] using hnot
        nlinarith [norm_nonneg (g b)]
      _ ≤ ∑ b, ‖g b‖ := Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)
      _ ≤ _ := hL1
  have hsplit : (∑ b ∈ E, ‖g b‖ ^ 2) +
      (∑ b ∈ Finset.univ \ E, ‖g b‖ ^ 2) = p := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ E), hL2]
    ring
  linarith

/-- The exact normalized residue transform satisfies the sparse-spectrum
conclusions used in Section 5 whenever its probability L1 norm is small. -/
theorem normalizedResidueTransform_sparse {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (ε δ : ℝ) (hδ : δ ≤ ε) (hδsq : δ ≤ ε ^ 2)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ δ) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    0 ∉ E ∧ (∀ b, -b ∈ E ↔ b ∈ E) ∧
      (E.card : ℝ) ≤ ε * p ∧
      (1 - ε ^ 2) * p ≤ ∑ b ∈ E, ‖normalizedResidueTransform S b‖ ^ 2 := by
  intro E
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hmass : (∑ b, ‖normalizedResidueTransform S b‖) ≤ δ * p := by
    have hh := mul_le_mul_of_nonneg_left hL1 hp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul, mul_comm (p : ℝ) δ] using hh
  obtain ⟨hc, he⟩ := largeTransformSpectrum_bounds _ δ hmass
    (normalizedResidueTransform_energy S hS hSp)
  refine ⟨largeTransformSpectrum_zero_not_mem _ (normalizedResidueTransform_zero S),
    largeTransformSpectrum_neg _ (normalizedResidueTransform_neg S),
    hc.trans (mul_le_mul_of_nonneg_right hδ hp.le), ?_⟩
  exact (mul_le_mul_of_nonneg_right (by linarith : 1 - ε ^ 2 ≤ 1 - δ) hp.le).trans he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem additiveFourier_reflect {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    additiveFourier (fun b => g (-b)) x = additiveFourier g (-x) := by
  simp only [additiveFourier_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.neg (ZMod p))
  intro b
  simp only [Equiv.neg_apply, neg_neg, neg_mul, mul_neg]

theorem densityFourierInverse_real {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (hg : ∀ b, g (-b) = conj (g b)) (x : ZMod p) :
    (densityFourierInverse g x).im = 0 := by
  have hr : (fun b => conj (g b)) = fun b => g (-b) := funext fun b => (hg b).symm
  have he := additiveFourier_conj g x
  rw [hr, additiveFourier_reflect] at he
  have hc : conj (densityFourierInverse g x) = densityFourierInverse g x := by
    unfold densityFourierInverse densityFourier
    rw [map_mul, Complex.conj_ofReal, ← he]
  have hh := congrArg Complex.im hc
  simp only [Complex.conj_im] at hh
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseAdditiveKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual additive kernel of the sparse spectral projection -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem sparseAdditiveKernel_formula {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (x : ZMod p) :
    sparseAdditiveKernel E t x = (t : ℂ) / p * ∑ b ∈ E, ZMod.stdAddChar (b * x) := by
  simp only [sparseAdditiveKernel, additiveFourier_apply, mul_neg, neg_neg,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, div_eq_mul_inv,
    mul_assoc]

theorem sparseAdditiveKernel_fourier {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (a : ZMod p) :
    additiveFourier (sparseAdditiveKernel E t) a =
      (t : ℂ) * (p : ℂ)⁻¹ * (if a ∈ E then 1 else 0) := by
  change additiveFourier (fun x => (t : ℂ) *
    additiveFourier (fun b => if b ∈ E then 1 else 0) (-x)) a = _
  rw [additiveFourier_const_mul, additiveFourier_reflect,
    additiveFourier_twice, neg_neg, ← mul_assoc]

theorem sparseAdditiveKernel_real {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) (x : ZMod p) :
    (sparseAdditiveKernel E t x).im = 0 := by
  have hr : (densityFourierInverse (fun b => if b ∈ E then (1 : ℂ) else 0) x).im = 0 := by
    apply densityFourierInverse_real
    intro b
    by_cases hb : b ∈ E <;> simp [hb, hE b]
  have hp : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p))).ne'
  change ((Real.sqrt (p : ℝ) : ℂ) *
    additiveFourier (fun b => if b ∈ E then 1 else 0) (-x)).im = 0 at hr
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hr
  have hz := (mul_eq_zero.mp hr).resolve_left hp
  simp only [sparseAdditiveKernel, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, hz, mul_zero]

theorem sparseAdditiveKernel_norm_le {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (ht : 0 ≤ t) (x : ZMod p) :
    ‖sparseAdditiveKernel E t x‖ ≤ t / p * E.card := by
  rw [sparseAdditiveKernel_formula, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ b ∈ E, ‖ZMod.stdAddChar (b * x)‖ := norm_sum_le _ _
    _ = _ := by
      simp [ZMod.stdAddChar_apply]
      simp only [Circle.norm_coe, Finset.sum_const, nsmul_eq_mul, mul_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_BilinearCube
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficients of a finite product of bilinear factors -/

namespace Ostmann
open scoped Classical BigOperators

theorem cubeDegree_le {n : ℕ} (t : BilinearCube n) (b : Bool) : cubeDegree t b ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (by intro i _; split_ifs <;> omega)
    _ = n := by simp

theorem cubeCoefficient_polynomial {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (A : BilinearCube n → E) (u v : ℂ) :
    finitePolynomial₂ (cubeCoefficient A) (n + 1) u v =
      ∑ t : BilinearCube n, (u ^ cubeDegree t false * v ^ cubeDegree t true) • A t := by
  unfold finitePolynomial₂ finitePolynomial cubeCoefficient
  simp_rw [Finset.smul_sum, smul_smul]
  calc
    _ = ∑ d ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
        ∑ t ∈ Finset.univ.filter (fun t => (cubeDegree t false, cubeDegree t true) = d),
          (u ^ cubeDegree t false * v ^ cubeDegree t true) • A t := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro t ht
      have he := (Finset.mem_filter.mp ht).2
      have h₁ : cubeDegree t false = i := congrArg Prod.fst he
      have h₂ : cubeDegree t true = j := congrArg Prod.snd he
      rw [h₁, h₂]
    _ = _ := by
      apply Finset.sum_fiberwise_of_maps_to
      intro t _
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (cubeDegree_le t false)),
          Finset.mem_range.mpr (Nat.lt_succ_of_le (cubeDegree_le t true))⟩

theorem cube_power_product {n : ℕ} (t : BilinearCube n) (b : Bool) (u : ℂ) :
    (∏ i, if (if b then (t i).2 else (t i).1) then u else 1) = u ^ cubeDegree t b := by
  unfold cubeDegree
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

theorem bilinear_product_expansion {n : ℕ}
    (W : Fin n → Bool × Bool → ℂ) (u v : ℂ) :
    (∏ i, (W i (false, false) + u * W i (true, false) +
      v * W i (false, true) + u * v * W i (true, true))) =
      finitePolynomial₂ (cubeCoefficient (fun t => ∏ i, W i (t i))) (n + 1) u v := by
  rw [cubeCoefficient_polynomial]
  have hl (i : Fin n) : (W i (false, false) + u * W i (true, false) +
      v * W i (false, true) + u * v * W i (true, true)) =
      ∑ b : Bool × Bool, (if b.1 then u else 1) * (if b.2 then v else 1) * W i b := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
    ring
  simp_rw [hl]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have h₁ : (∏ i, if (t i).1 then u else 1) = u ^ cubeDegree t false := by
    simpa only [Bool.false_eq_true, ite_false, if_false] using cube_power_product t false u
  have h₂ : (∏ i, if (t i).2 then v else 1) = v ^ cubeDegree t true := by
    simpa only [ite_true, if_true] using cube_power_product t true v
  rw [h₁, h₂]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Energy bounds for the sparse kernel and its pointwise square -/

namespace Ostmann
open scoped Classical BigOperators

theorem sparseAdditiveKernel_square_fourier {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (a : ZMod p) :
    additiveFourier (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) a =
      (t : ℂ) ^ 2 * ((p : ℂ)⁻¹) ^ 2 * ((E.filter fun b => a - b ∈ E).card : ℂ) := by
  rw [additiveFourier_pointwise_mul]
  simp_rw [sparseAdditiveKernel_fourier]
  have he (b : ZMod p) :
      ((t : ℂ) * (p : ℂ)⁻¹ * (if b ∈ E then 1 else 0)) *
        ((t : ℂ) * (p : ℂ)⁻¹ * (if a - b ∈ E then 1 else 0)) =
      ((t : ℂ) ^ 2 * ((p : ℂ)⁻¹) ^ 2) *
        (if b ∈ E ∧ a - b ∈ E then 1 else 0) := by
    split_ifs <;> simp_all
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  congr 1
  simp [← Finset.filter_filter]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact nonzero-residue sums for the sparse additive kernel -/

namespace Ostmann
open scoped Classical BigOperators

theorem sum_eq_mul_additiveFourier_zero {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ x, f x) = (p : ℂ) * additiveFourier f 0 := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  simp only [additiveFourier_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one,
    ← mul_assoc, mul_inv_cancel₀ hp, one_mul]

theorem sparseAdditiveKernel_zero {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) :
    sparseAdditiveKernel E t 0 = (t : ℂ) * E.card / p := by
  rw [sparseAdditiveKernel_formula]
  simp only [mul_zero, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

theorem sparseAdditiveKernel_sum {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (t : ℝ) :
    (∑ x, sparseAdditiveKernel E t x) = 0 := by
  rw [sum_eq_mul_additiveFourier_zero, sparseAdditiveKernel_fourier,
    ite_eq_right hE, mul_zero, mul_zero]

theorem sparseAdditiveKernel_sum_nonzero {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (t : ℝ) :
    (∑ x ∈ Finset.univ.erase 0, sparseAdditiveKernel E t x) = -(t : ℂ) * E.card / p := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sparseAdditiveKernel_sum E hE,
    sparseAdditiveKernel_zero]
  ring

theorem sparseAdditiveKernel_square_sum {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) :
    (∑ x, sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) =
      (t : ℂ) ^ 2 * E.card / p := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have he : E.filter (fun b => (0 : ZMod p) - b ∈ E) = E := by
    ext b
    simp only [Finset.mem_filter, zero_sub, hE b, and_self]
  rw [sum_eq_mul_additiveFourier_zero, sparseAdditiveKernel_square_fourier, he]
  field_simp

theorem sparseAdditiveKernel_square_sum_nonzero {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) :
    (∑ x ∈ Finset.univ.erase 0, sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) =
      (t : ℂ) ^ 2 * ((E.card : ℂ) / p - ((E.card : ℂ) / p) ^ 2) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sparseAdditiveKernel_square_sum E hE,
    sparseAdditiveKernel_zero]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseMellinCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicative coefficients of the actual sparse additive kernel -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem sum_units_eq_sum_nonzero {p : ℕ} [Fact p.Prime]
    {R : Type*} [AddCommMonoid R] (f : ZMod p → R) :
    (∑ u : (ZMod p)ˣ, f u) = ∑ x ∈ Finset.univ.erase 0, f x := by
  apply Finset.sum_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p))
  · intro u _
    exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
  · intro u _ v _ huv
    exact Units.val_injective huv
  · intro x hx
    exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl

theorem sparseAdditiveKernel_total_energy {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) :
    (∑ x, ‖sparseAdditiveKernel E t x‖ ^ 2) = t ^ 2 * E.card / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hh := additiveFourier_parseval (sparseAdditiveKernel E t)
  simp_rw [sparseAdditiveKernel_fourier, norm_mul, norm_inv, Complex.norm_real,
    Complex.norm_natCast, Real.norm_eq_abs, mul_pow, sq_abs] at hh
  have hs : (∑ a : ZMod p, ‖if a ∈ E then (1 : ℂ) else 0‖ ^ 2) = (E.card : ℝ) := by
    calc
      _ = ∑ a : ZMod p, if a ∈ E then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp_all
      _ = _ := by simp
  simp_rw [← Finset.mul_sum, hs] at hh
  field_simp at hh
  apply (eq_div_iff hp.ne').mpr
  nlinarith

attribute [local instance] OAI.Ostmann.instFintypeMulCharZModComplexOfFactPrime_solutions_3
theorem mellinCoefficient_sq_le_energy {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)ˣ → ℂ) (χ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient f χ‖ ^ 2 ≤
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ x, ‖f x‖ ^ 2 := by
  rw [← mellin_parseval]
  exact Finset.single_le_sum (fun ψ _ => sq_nonneg ‖mellinCoefficient f ψ‖) (Finset.mem_univ χ)

/-- Both powers used by the squared truncation have the same square-root
coefficient bound. The proof uses exact Parseval and `|b|<=1`. -/
theorem sparse_power_mellin_sq_le {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (j : ℕ) (hj : j = 1 ∨ j = 2) (χ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ j) χ‖ ^ 2 ≤
      2 / p := by
  have hpN := (Fact.out : p.Prime).two_le
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast hpN
  have hp0 : (0 : ℝ) < p := by linarith
  have hcard : (E.card : ℝ) ≤ p := by
    have hh := Finset.card_le_card (Finset.subset_univ E)
    have hh' : E.card ≤ p := by simpa only [Finset.card_univ, ZMod.card] using hh
    exact_mod_cast hh'
  have hnorm (x : ZMod p) : ‖sparseAdditiveKernel E t x‖ ≤ 1 := by
    have hh := sparseAdditiveKernel_norm_le E t ht x
    have hh' : t / p * E.card ≤ 1 := by
      have hc := (div_le_one hp0).mpr hcard
      calc
        _ = t * ((E.card : ℝ) / p) := by ring
        _ ≤ 1 * 1 := mul_le_mul ht1 hc (by positivity) (by norm_num)
        _ = 1 := by ring
    exact hh.trans hh'
  have henergy : (∑ u : (ZMod p)ˣ, ‖sparseAdditiveKernel E t u ^ j‖ ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ u : (ZMod p)ˣ, ‖sparseAdditiveKernel E t u‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro u _
        rcases hj with rfl | rfl
        · simp
        · rw [norm_pow]
          have hsq : ‖sparseAdditiveKernel E t u‖ ^ 2 ≤ 1 := by
            nlinarith [hnorm u, norm_nonneg (sparseAdditiveKernel E t u)]
          nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖sparseAdditiveKernel E t u‖)]
      _ = ∑ x ∈ Finset.univ.erase 0, ‖sparseAdditiveKernel E t x‖ ^ 2 :=
        sum_units_eq_sum_nonzero (fun x : ZMod p => ‖sparseAdditiveKernel E t x‖ ^ 2)
      _ ≤ ∑ x, ‖sparseAdditiveKernel E t x‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => sq_nonneg _)
      _ = t ^ 2 * E.card / p := sparseAdditiveKernel_total_energy E t
      _ ≤ 1 := by
        apply (div_le_one hp0).mpr
        have ht2 : t ^ 2 ≤ 1 := by nlinarith
        nlinarith
  have hh := mellinCoefficient_sq_le_energy
    (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ j) χ
  have hc : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hc] at hh
  calc
    _ ≤ ((p : ℝ) - 1)⁻¹ * 1 := hh.trans (mul_le_mul_of_nonneg_left henergy (inv_nonneg.mpr (by linarith)))
    _ ≤ 2 / p := by
      rw [mul_one, inv_eq_one_div]
      apply (div_le_div_iff₀ (by linarith) hp0).mpr
      linarith

/-- A convenient non-squared bound for the two local powers. -/
theorem sparse_power_mellin_le {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (j : ℕ) (hj : j = 1 ∨ j = 2) (χ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ j) χ‖ ≤
      2 / Real.sqrt (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs := Real.sqrt_pos.mpr hp
  have hh := sparse_power_mellin_sq_le E t ht ht1 j hj χ
  have hm := (le_div_iff₀ hp).mp hh
  apply (le_div_iff₀ hs).mpr
  have he : (‖mellinCoefficient (fun x : (ZMod p)ˣ =>
      sparseAdditiveKernel E t x ^ j) χ‖ * Real.sqrt (p : ℝ)) ^ 2 ≤ 2 := by
    rw [mul_pow, Real.sq_sqrt hp.le]
    exact hm
  nlinarith [mul_nonneg (norm_nonneg (mellinCoefficient
    (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ j) χ)) hs.le]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SparsePrincipalCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smaller principal coefficients of the sparse kernel -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem sparse_mellin_principal {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (t : ℝ) :
    mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x) 1 =
      (((p : ℝ) - 1)⁻¹ * (-t * E.card / p) : ℝ) := by
  have hc : (Fintype.card (ZMod p)ˣ : ℂ) = (p : ℂ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  simp only [mellinCoefficient, MulChar.one_apply_coe, map_one, mul_one]
  rw [sum_units_eq_sum_nonzero, sparseAdditiveKernel_sum_nonzero E hE, hc]
  push_cast
  ring

theorem sparse_square_mellin_principal {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (hsym : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) :
    mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ 2) 1 =
      (((p : ℝ) - 1)⁻¹ * (t ^ 2 * ((E.card : ℝ) / p - ((E.card : ℝ) / p) ^ 2)) : ℝ) := by
  have hc : (Fintype.card (ZMod p)ˣ : ℂ) = (p : ℂ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  simp only [mellinCoefficient, MulChar.one_apply_coe, map_one, mul_one]
  rw [sum_units_eq_sum_nonzero (fun x : ZMod p => sparseAdditiveKernel E t x ^ 2)]
  simp_rw [pow_two]
  rw [sparseAdditiveKernel_square_sum_nonzero E hsym, hc]
  push_cast
  ring

theorem sparse_principal_coefficients_le {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (hsym : ∀ b, -b ∈ E ↔ b ∈ E)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (j : ℕ) (hj : j = 1 ∨ j = 2) :
    ‖mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ j) 1‖ ≤
      2 / p := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hc : (E.card : ℝ) ≤ p := by
    have hh := Finset.card_le_card (Finset.subset_univ E)
    have hh' : E.card ≤ p := by simpa only [Finset.card_univ, ZMod.card] using hh
    exact_mod_cast hh'
  have he0 : 0 ≤ (E.card : ℝ) / p := by positivity
  have he1 : (E.card : ℝ) / p ≤ 1 := (div_le_one hp0).mpr hc
  have hi : ((p : ℝ) - 1)⁻¹ ≤ 2 / p := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hp1 hp0).mpr
    linarith
  apply le_trans _ hi
  rcases hj with rfl | rfl
  · simp only [pow_one, sparse_mellin_principal E hE t, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hp1), abs_div, abs_neg,
      abs_of_nonneg ht, abs_of_nonneg (show (0 : ℝ) ≤ E.card from Nat.cast_nonneg _), abs_of_pos hp0]
    have hh : t * E.card / p ≤ 1 := by
      calc
        _ = t * ((E.card : ℝ) / p) := by ring
        _ ≤ 1 * 1 := mul_le_mul ht1 he1 he0 (by norm_num)
        _ = 1 := by ring
    exact mul_le_of_le_one_right (inv_nonneg.mpr hp1.le) hh
  · rw [sparse_square_mellin_principal E hsym t, Complex.norm_real, Real.norm_eq_abs]
    have hn : 0 ≤ (E.card : ℝ) / p - ((E.card : ℝ) / p) ^ 2 := by nlinarith
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hp1.le) (mul_nonneg (sq_nonneg _) hn))]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have hh : t ^ 2 * ((E.card : ℝ) / p - ((E.card : ℝ) / p) ^ 2) ≤ 1 := by
      nlinarith [mul_le_mul ht2 (show (E.card : ℝ) / p - ((E.card : ℝ) / p) ^ 2 ≤ 1 by nlinarith)
        hn (by norm_num : (0 : ℝ) ≤ 1)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hp1.le) hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseCoefficientMajorant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform coefficient bound for the truncated sparse weight -/
namespace Ostmann
open scoped Classical BigOperators

theorem sparsePatternMellin_norm_sum {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (hsym : ∀ b, -b ∈ E ↔ b ∈ E)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hp : (36 : ℝ) ≤ p)
    (χ : MulChar (ZMod p) ℂ) :
    (∑ b : Bool × Bool, ‖sparsePatternMellin E t χ b‖) ≤ 1 + 6 / p := by
  have hp0 : (0 : ℝ) < p := by linarith
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, sparsePatternMellin]
  by_cases hχ : χ = 1
  · subst χ
    have h₁ := sparse_principal_coefficients_le E hE hsym t ht ht1 1 (Or.inl rfl)
    have h₂ := sparse_principal_coefficients_le E hE hsym t ht ht1 2 (Or.inr rfl)
    simp only [pow_one] at h₁
    simp only [ite_true, if_true, norm_one]
    ring_nf at h₁ h₂ ⊢
    linarith
  · have h₁ := sparse_power_mellin_le E t ht ht1 1 (Or.inl rfl) χ
    have h₂ := sparse_power_mellin_le E t ht ht1 2 (Or.inr rfl) χ
    simp only [pow_one] at h₁
    simp only [hχ, ite_false, if_false, norm_zero]
    have hs : 6 ≤ Real.sqrt (p : ℝ) := (Real.le_sqrt (by norm_num) hp0.le).mpr (by nlinarith)
    have hs0 : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
    have hh : 6 / Real.sqrt (p : ℝ) ≤ 1 := (div_le_one hs0).mpr hs
    have hh' : 0 ≤ 6 / (p : ℝ) := by positivity
    ring_nf at h₁ h₂ hh hh' ⊢
    linarith

/-- The norm of each full multiplicative coefficient is at most exp(6H),
independently of the truncation order and of the number of primes. -/
theorem sparseTruncatedMellinCoefficient_norm_le {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] (E : ∀ i, Finset (ZMod (p i)))
    (hE : ∀ i, 0 ∉ E i) (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hp : ∀ i, (36 : ℝ) ≤ p i)
    (K : ℕ) (χ : ∀ i, MulChar (ZMod (p i)) ℂ) :
    ‖sparseTruncatedMellinCoefficient p E t K χ‖ ≤
      Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) := by
  unfold sparseTruncatedMellinCoefficient
  calc
    _ ≤ ∑ v ∈ (Finset.univ : Finset (BilinearCube n)).filter
        (fun v => cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K),
        ∏ i, ‖sparsePatternMellin (E i) t (χ i) (v i)‖ := by
      simpa only [norm_prod] using norm_sum_le
        ((Finset.univ : Finset (BilinearCube n)).filter
          (fun v => cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K))
        (fun v => ∏ i, sparsePatternMellin (E i) t (χ i) (v i))
    _ ≤ ∑ v : BilinearCube n, ∏ i, ‖sparsePatternMellin (E i) t (χ i) (v i)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ = ∏ i, ∑ b : Bool × Bool, ‖sparsePatternMellin (E i) t (χ i) b‖ :=
      (Fintype.prod_sum (fun (i : Fin n) (b : Bool × Bool) =>
        ‖sparsePatternMellin (E i) t (χ i) b‖)).symm
    _ ≤ ∏ i, (1 + 6 / (p i : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      · intro i _
        exact sparsePatternMellin_norm_sum (E i) (hE i) (hsym i) t ht ht1 (hp i) (χ i)
    _ ≤ ∏ i, Real.exp (6 / (p i : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        linarith [Real.add_one_le_exp (6 / (p i : ℝ))]
    _ = _ := by rw [← Real.exp_sum]; simp only [div_eq_mul_inv, ← Finset.mul_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexLowZeroBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The low-zero Laplace estimate from the published density theorem -/

namespace Ostmann
open scoped Classical BigOperators

theorem complex_zero_density_exponential
    (Z : ∀ χ, ComplexZeroEnumeration χ) {C : ℝ} (hC : 0 ≤ C)
    (hdensity : ∀ (Q : ℕ), 1 ≤ Q → ∀ (T σ : ℝ), 2 ≤ T →
      1 / 2 ≤ σ → σ ≤ 1 → ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((Z χ).count σ T : ℝ)) ≤
        C * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ)) *
          (Real.log ((Q : ℝ) * T)) ^ 13)
    (Q : ℕ) (hQ : 1 ≤ Q) (T y : ℝ) (hT : 2 ≤ T) (hy : 0 ≤ y) (hy' : y ≤ 1 / 2)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q) :
    (∑ χ ∈ F, ((Z χ).count (1 - y) T : ℝ)) ≤
      (C * (Real.log ((Q : ℝ) * T)) ^ 13) *
        Real.exp ((3 * Real.log ((Q : ℝ) ^ 2 * T)) * y) := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hbase : 1 ≤ (Q : ℝ) ^ 2 * T := by nlinarith
  have hlog : 0 ≤ Real.log ((Q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  have hexp : 3 * (1 - (1 - y)) / (2 - (1 - y)) ≤ 3 * y := by
    calc
      _ = 3 * y / (1 + y) := by congr 1 <;> ring
      _ ≤ 3 * y := div_le_self (by positivity) (by linarith)
  have hp := Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hd := hdensity Q hQ T (1 - y) hT (by linarith) (by linarith) F hF
  apply hd.trans
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC)
    (pow_nonneg hlog 13)
  have he : ((Q : ℝ) ^ 2 * T) ^ (3 * y) =
      Real.exp ((3 * Real.log ((Q : ℝ) ^ 2 * T)) * y) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < (Q : ℝ) ^ 2 * T)]
    congr 1
    ring
  rw [he] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem lowZeroIndices_count_bound
    (Z : ∀ χ, ComplexZeroEnumeration χ) (F : Finset PrimitiveComplexCharacter)
    (T A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 →
      (∑ χ ∈ F, ((Z χ).count (1 - y) T : ℝ)) ≤ B * Real.exp (A * y)) :
    ∀ t : ℝ, 0 ≤ t →
      (((lowZeroIndices Z F T).filter
        (fun z => 1 - ((Z z.1).zeros z.2).re ≤ t)).card : ℝ) ≤ B * Real.exp (A * t) := by
  intro t ht
  let y := min t (1 / 2 : ℝ)
  have hy : 0 ≤ y := le_min ht (by norm_num)
  have hy' : y ≤ 1 / 2 := min_le_right _ _
  have hsub : (lowZeroIndices Z F T).filter
      (fun z => 1 - ((Z z.1).zeros z.2).re ≤ t) ⊆
      F.sigma (fun χ => ((Z χ).heightIndices T).filter
        (fun i => 1 - y ≤ ((Z χ).zeros i).re)) := by
    intro z hz
    obtain ⟨hz, hgap⟩ := Finset.mem_filter.mp hz
    obtain ⟨hχ, hi⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hi, hre⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_sigma.mpr
    refine ⟨hχ, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
    have hh : 1 - ((Z z.1).zeros z.2).re ≤ y := le_min hgap (by linarith)
    linarith
  calc
    _ ≤ ((F.sigma (fun χ => ((Z χ).heightIndices T).filter
        (fun i => 1 - y ≤ ((Z χ).zeros i).re))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = ∑ χ ∈ F, ((Z χ).count (1 - y) T : ℝ) := by
      rw [Finset.card_sigma, Nat.cast_sum]
      rfl
    _ ≤ B * Real.exp (A * y) := hd y hy hy'
    _ ≤ B * Real.exp (A * t) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_left _ _) hA)) hB

theorem low_zero_laplace_bound
    (Z : ∀ χ, ComplexZeroEnumeration χ) (F : Finset PrimitiveComplexCharacter)
    (T A B M u : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 4 * A ≤ M) (hu : 0 ≤ u)
    (hgap : ∀ χ ∈ F, ∀ i ∈ (Z χ).heightIndices T, u ≤ 1 - ((Z χ).zeros i).re)
    (hd : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 →
      (∑ χ ∈ F, ((Z χ).count (1 - y) T : ℝ)) ≤ B * Real.exp (A * y)) :
    (∑ χ ∈ F, ∑ i ∈ ((Z χ).heightIndices T).filter
      (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
        Real.exp (-M * (1 - ((Z χ).zeros i).re))) ≤
      2 * B ^ 2 * Real.exp (-(M * u) / 2) := by
  have hh := finite_laplace_density_bound (lowZeroIndices Z F T)
    (fun z => 1 - ((Z z.1).zeros z.2).re) A B M u hA hB hM hu
    (fun z hz => hgap z.1 (Finset.mem_sigma.mp hz).1 z.2
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).1)
    (lowZeroIndices_count_bound Z F T A B hA hB hd)
  simpa only [lowZeroIndices, Finset.sum_sigma] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RetainedLowZeroEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained low-zero sum, derived from two published inputs -/

namespace Ostmann
open scoped Classical BigOperators

theorem retained_low_zero_estimate (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ Q : ℕ, 101 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ F : Finset PrimitiveComplexCharacter,
        (∀ χ ∈ F, χ.modulus ≤ Q) →
        (∀ χ ∈ F, some χ ≠ exception) →
        ∀ M : ℝ, 12 * Real.log ((Q : ℝ) ^ 2 * T) ≤ M →
        (∑ χ ∈ F, ∑ i ∈ ((Z χ).heightIndices T).filter
          (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
            Real.exp (-M * (1 - ((Z χ).zeros i).re))) ≤
          2 * (C * (Real.log ((Q : ℝ) * T)) ^ 13) ^ 2 *
            Real.exp (-(M * (c / Real.log (2 * (Q : ℝ) * T))) / 2) := by
  obtain ⟨C, hC, hD⟩ := hD
  obtain ⟨c, hc, hR⟩ := hR
  refine ⟨C, c, hC, hc, ?_⟩
  intro Q hQ T hT
  obtain ⟨exception, hexc⟩ := hR Q hQ T hT
  refine ⟨exception, ?_⟩
  intro F hF hFE M hM
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hbase : 1 ≤ (Q : ℝ) ^ 2 * T := by nlinarith
  have hlog : 0 ≤ Real.log ((Q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  have hden : 0 < Real.log (2 * (Q : ℝ) * T) := Real.log_pos (by nlinarith)
  apply low_zero_laplace_bound Z F T
    (3 * Real.log ((Q : ℝ) ^ 2 * T))
    (C * (Real.log ((Q : ℝ) * T)) ^ 13) M
    (c / Real.log (2 * (Q : ℝ) * T))
  · exact mul_nonneg (by norm_num) (Real.log_nonneg hbase)
  · exact mul_nonneg hC.le (pow_nonneg hlog _)
  · linarith
  · exact (div_pos hc hden).le
  · intro χ hχ i hi
    exact hexc χ (hF χ hχ) (hFE χ hχ) i
      (((Z χ).mem_heightIndices T i).mp hi)
  · intro y hy hy'
    exact complex_zero_density_exponential Z hC.le hD Q (by omega) T y hT hy hy' F hF

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LowZeroDecayRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The low-zero contribution at the actual growing conductor cutoff -/

namespace Ostmann
open Filter

theorem eventual_low_zero_error (C c a D : ℝ) (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      2 * (C * (6 * q) ^ 13) ^ 2 *
        Real.exp (-(Real.exp L * (c / (Real.log 2 + 6 * q))) / 2) ≤
          Real.exp (-D * L) := by
  let b := 2 + 6 * a
  let E := max (D + 25) 1
  have hb : 0 < b := by dsimp [b]; linarith
  have hE : 0 < E := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop 26
    (show (0 : ℝ) < 8 / 5 by norm_num)).const_mul_left (2 * C ^ 2 * (6 * a) ^ 26)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hfast := ((isLittleO_pow_exp_pos_mul_atTop 2
    (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul_left (2 * b * E)).bound hc
  filter_upwards [hpoly, hfast, eventually_ge_atTop (1 : ℝ)] with L hpoly hfast hL
  intro q hq hqa
  have hLp : 0 < L := by linarith
  have hpoly' : 2 * C ^ 2 * (6 * a) ^ 26 * L ^ 26 ≤ Real.exp ((8 / 5 : ℝ) * L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (2 * C ^ 2 * (6 * a) ^ 26) * L ^ 26),
      abs_of_pos (Real.exp_pos _), one_mul] using hpoly
  have hfast' : 2 * b * E * L ^ 2 ≤ c * Real.exp ((1 / 10 : ℝ) * L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * b * E * L ^ 2),
      abs_of_pos (Real.exp_pos _)] using hfast
  have hden0 : 0 < Real.log 2 + 6 * q := by
    have hh : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hden : Real.log 2 + 6 * q ≤ b * L * Real.exp ((9 / 10 : ℝ) * L) := by
    have he : 1 ≤ Real.exp ((9 / 10 : ℝ) * L) := Real.one_le_exp (by positivity)
    have hprod : 1 ≤ L * Real.exp ((9 / 10 : ℝ) * L) :=
      hL.trans (le_mul_of_one_le_right hLp.le he)
    have hl : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    dsimp [b]
    nlinarith
  have hexp : Real.exp ((1 / 10 : ℝ) * L) * Real.exp ((9 / 10 : ℝ) * L) =
      Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hgap : E * L ≤ (Real.exp L * (c / (Real.log 2 + 6 * q))) / 2 := by
    have hm := mul_le_mul_of_nonneg_right hfast' (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    rw [mul_assoc c, hexp] at hm
    have hd := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 2 * E * L)
    have hf : (E * L) * (2 * (Real.log 2 + 6 * q)) ≤ Real.exp L * c := by
      nlinarith [hm, hd]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden0).mpr
    convert hf using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hcoefficient : 2 * (C * (6 * q) ^ 13) ^ 2 ≤ Real.exp (25 * L) := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 6 * q)
      (show 6 * q ≤ 6 * (a * L * Real.exp ((9 / 10 : ℝ) * L)) by linarith [hqa]) 26
    have hm := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * C ^ 2)
    have hpowexp : Real.exp ((9 / 10 : ℝ) * L) ^ 26 =
        Real.exp ((117 / 5 : ℝ) * L) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hbnd : 2 * (C * (6 * q) ^ 13) ^ 2 ≤
        (2 * C ^ 2 * (6 * a) ^ 26 * L ^ 26) * Real.exp ((117 / 5 : ℝ) * L) := by
      convert hm using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [mul_pow, hpowexp] <;> ring)
    calc
      _ ≤ _ := hbnd
      _ ≤ Real.exp ((8 / 5 : ℝ) * L) * Real.exp ((117 / 5 : ℝ) * L) :=
        mul_le_mul_of_nonneg_right hpoly' (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp (25 * L) * Real.exp (-E * L) := mul_le_mul hcoefficient
      (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((25 - E) * L) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_right (le_max_left (D + 25) 1) hLp.le
      dsimp [E]
      linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothMeanDecayRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical decay for the remaining terms of the smooth explicit formula -/
namespace Ostmann
open Filter

/-- The conductor grows more slowly than `log X = exp L`. -/
theorem eventual_conductor_exponential_decay (a b C D : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℝ, 0 ≤ q →
      q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      C * Real.exp (b * q - Real.exp L / 2) ≤ Real.exp (-D * L) := by
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul_left (4 * b * a)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hlin := ((isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 1 by norm_num)).const_mul_left (4 * |D + 1|)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hsmall, hlin, Real.tendsto_exp_atTop.eventually_ge_atTop C,
    eventually_ge_atTop (1 : ℝ)] with L hs hl hcoef hL
  intro q _ hq
  have hs' : 4 * b * a * L ≤ Real.exp ((1 / 10 : ℝ) * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 4 * b * a * L), abs_of_pos (Real.exp_pos _), one_mul] using hs
  have hl' : 4 * |D + 1| * L ≤ Real.exp L := by
    simpa only [pow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 4 * |D + 1| * L), abs_of_pos (Real.exp_pos _)] using hl
  have hg : b * q ≤ Real.exp L / 4 := by
    have hm := mul_le_mul_of_nonneg_right hs' (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    have he : Real.exp ((1 / 10 : ℝ) * L) * Real.exp ((9 / 10 : ℝ) * L) =
        Real.exp L := by rw [← Real.exp_add]; congr 1; ring
    rw [he] at hm
    have hmq := mul_le_mul_of_nonneg_left hq hb
    nlinarith
  calc
    _ ≤ Real.exp L * Real.exp (b * q - Real.exp L / 2) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = Real.exp (L + b * q - Real.exp L / 2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_right (le_abs_self (D + 1)) (by linarith : 0 ≤ L)
      linarith)

/-- The high-zero tail decays when `log Q` is at least `L²`. -/
theorem eventual_conductor_negative_decay (C D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℝ, L ^ 2 ≤ q →
      C * Real.exp (-q) ≤ Real.exp (-D * L) := by
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop C,
    eventually_ge_atTop (max 1 (D + 1))] with L hC' hL
  intro q hq
  have hL0 : 0 ≤ L := le_trans (by norm_num) ((le_max_left _ _).trans hL)
  have hDL : (D + 1) * L ≤ L ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hL) hL0
    nlinarith
  calc
    _ ≤ Real.exp L * Real.exp (-q) := mul_le_mul_of_nonneg_right hC' (Real.exp_nonneg _)
    _ = Real.exp (L - q) := by rw [← Real.exp_add]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseConductorCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integral conductor cutoff in (5.14) -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem sparseConductorCutoff_pos (C L : ℝ) : 0 < sparseConductorCutoff C L :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

theorem sparseConductorCutoff_log_lower (C L : ℝ) :
    2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L) ≤
      Real.log (sparseConductorCutoff C L) := by
  have hh := Nat.le_ceil (Real.exp
    (2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L)))
  have hp := Real.log_le_log (Real.exp_pos _) hh
  simpa only [Real.log_exp, sparseConductorCutoff] using hp

theorem sparseConductorCutoff_log_upper (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L) :
    Real.log (sparseConductorCutoff C L) ≤ (2 * C + 3) * L * Real.exp ((9 / 10 : ℝ) * L) := by
  let S := 2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have he : 1 ≤ Real.exp S := Real.one_le_exp hS
  have hc := Nat.ceil_lt_add_one (Real.exp_nonneg S)
  have hc' : (sparseConductorCutoff C L : ℝ) ≤ 2 * Real.exp S := by
    dsimp [sparseConductorCutoff]
    change (⌈Real.exp S⌉₊ : ℝ) ≤ _
    linarith
  have hp : 0 < (sparseConductorCutoff C L : ℝ) := by
    exact_mod_cast sparseConductorCutoff_pos C L
  have hlog := Real.log_le_log hp hc'
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hk : (sparseTruncationDegree C L : ℝ) ≤ C * L + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hC (by linarith))).le
  have hEL : 1 ≤ Real.exp ((9 / 10 : ℝ) * L) := Real.one_le_exp (by positivity)
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  dsimp [S] at hlog
  have hmul := mul_le_mul_of_nonneg_right hk (Real.exp_nonneg ((9 / 10 : ℝ) * L))
  nlinarith

theorem eventual_sparseConductorCutoff (C : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, 101 ≤ sparseConductorCutoff C L ∧
      L ^ 2 ≤ Real.log (sparseConductorCutoff C L) ∧
      Real.log (sparseConductorCutoff C L) ≤
        (2 * C + 3) * L * Real.exp ((9 / 10 : ℝ) * L) := by
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 9 / 10 by norm_num))).bound (show 0 < 2 * C by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (11 : ℝ)] with L hs hL
  have hL0 : 0 ≤ L := by linarith
  have hs' : L ≤ 2 * C * Real.exp ((9 / 10 : ℝ) * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg hL0,
      abs_of_pos (Real.exp_pos _)] using hs
  have hk : C * L ≤ (sparseTruncationDegree C L : ℝ) := Nat.le_ceil _
  have hlower : L ^ 2 ≤ Real.log (sparseConductorCutoff C L) := by
    have hmul := mul_le_mul_of_nonneg_right hs' hL0
    have hmul' := mul_le_mul_of_nonneg_right hk (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    have hh := sparseConductorCutoff_log_lower C L
    nlinarith
  have hpos : 0 < (sparseConductorCutoff C L : ℝ) := by
    exact_mod_cast sparseConductorCutoff_pos C L
  have hnum : (101 : ℝ) ≤ sparseConductorCutoff C L := by
    have hh := Real.log_le_self hpos.le
    nlinarith
  exact ⟨by exact_mod_cast hnum, hlower, sparseConductorCutoff_log_upper C L hC.le (by linarith)⟩

theorem sparse_product_le_conductor_cutoff {ι : Type*} (S : Finset ι) (p : ι → ℕ)
    (C L : ℝ) (hp : ∀ i ∈ S, 0 < p i)
    (hlog : ∀ i ∈ S, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L))
    (hcard : S.card ≤ 2 * sparseTruncationDegree C L) :
    ∏ i ∈ S, p i ≤ sparseConductorCutoff C L := by
  have hprod : (0 : ℝ) < ∏ i ∈ S, (p i : ℝ) :=
    Finset.prod_pos (fun i hi => by exact_mod_cast hp i hi)
  have hsum : (∑ i ∈ S, Real.log (p i)) ≤
      2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L) := by
    calc
      _ ≤ ∑ _i ∈ S, Real.exp ((9 / 10 : ℝ) * L) := Finset.sum_le_sum hlog
      _ = (S.card : ℝ) * Real.exp ((9 / 10 : ℝ) * L) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_nonneg _)
  have he : (∏ i ∈ S, (p i : ℝ)) ≤ Real.exp
      (2 * (sparseTruncationDegree C L : ℝ) * Real.exp ((9 / 10 : ℝ) * L)) := by
    apply (Real.log_le_iff_le_exp hprod).mp
    rw [Real.log_prod (fun i hi => (by exact_mod_cast (hp i hi).ne' : (p i : ℝ) ≠ 0))]
    exact hsum
  have hh : (∏ i ∈ S, (p i : ℝ)) ≤ (sparseConductorCutoff C L : ℝ) :=
    he.trans (Nat.le_ceil _)
  exact_mod_cast hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseProductCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product characters and their active conductor support -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_prod_apply {I : Type*} {N : ℕ} (S : Finset I)
    (χ : I → DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    (∏ i ∈ S, χ i) u = ∏ i ∈ S, χ i u := by
  induction S using Finset.induction_on with
  | empty => simp [MulChar.one_apply_coe]
  | @insert i S hi ih => simp only [Finset.prod_insert hi, MulChar.mul_apply, ih]

theorem sparseProductCharacter_apply {I : Type*} [Fintype I]
    (p : I → ℕ) (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (u : (ZMod (∏ i, p i))ˣ) :
    sparseProductCharacter p χ u = ∏ i, χ i (crtUnitEquiv p hc u i) := by
  rw [sparseProductCharacter, character_prod_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [crtUnitEquiv_apply]
  simp only [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
    MulChar.coe_toUnitHom, ZMod.unitsMap_def]
  rfl

theorem sparseProductCharacter_injective {I : Type*} [Fintype I]
    (p : I → ℕ) (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Function.Injective (sparseProductCharacter p) := by
  intro χ ψ he
  funext i
  apply MulChar.ext
  intro u
  let x : ∀ j, (ZMod (p j))ˣ := Pi.mulSingle i u
  have hh := congrArg (fun c : DirichletCharacter ℂ (∏ j, p j) =>
    c ((crtUnitEquiv p hc).symm x)) he
  simp only [sparseProductCharacter_apply p hc, MulEquiv.apply_symm_apply] at hh
  have hprod (θ : ∀ j, DirichletCharacter ℂ (p j)) : (∏ j, θ j (x j)) = θ i u := by
    calc
      _ = θ i (x i) := by
        apply Finset.prod_eq_single i
        · intro j _ hji
          simp [x, Pi.mulSingle, hji, MulChar.map_one]
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      _ = _ := by simp [x, Pi.mulSingle]
  rw [hprod, hprod] at hh
  exact hh

theorem sparseProductCharacter_factorsThrough {I : Type*} [Fintype I]
    (p : I → ℕ) (χ : ∀ i, DirichletCharacter ℂ (p i)) (S : Finset I)
    (hχ : ∀ i, i ∉ S → χ i = 1) :
    (sparseProductCharacter p χ).FactorsThrough (∏ i ∈ S, p i) := by
  have hSN : (∏ i ∈ S, p i) ∣ ∏ i, p i :=
    Finset.prod_dvd_prod_of_subset S Finset.univ p S.subset_univ
  let ψ : DirichletCharacter ℂ (∏ i ∈ S, p i) :=
    ∏ i : S, DirichletCharacter.changeLevel (Finset.dvd_prod_of_mem p i.property) (χ i)
  refine ⟨hSN, ψ, ?_⟩
  rw [show DirichletCharacter.changeLevel hSN ψ =
      ∏ i ∈ S, DirichletCharacter.changeLevel (Finset.dvd_prod_of_mem p (Finset.mem_univ i))
        (χ i) by
    dsimp [ψ]
    rw [map_prod]
    calc
      _ = ∏ i : S, DirichletCharacter.changeLevel
          (Finset.dvd_prod_of_mem p (Finset.mem_univ i.val)) (χ i) := by
        apply Finset.prod_congr rfl
        intro i _
        exact (DirichletCharacter.changeLevel_trans (χ i) _ hSN).symm
      _ = _ := Finset.prod_coe_sort S (fun i : I => DirichletCharacter.changeLevel
        (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (χ i))]
  symm
  change (∏ i ∈ S, _) = ∏ i, _
  apply Finset.prod_subset S.subset_univ
  intro i _ hi
  rw [hχ i hi, map_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseCoefficientSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero coefficients have the manuscript's short conductor support -/
namespace Ostmann
open scoped Classical BigOperators

theorem sparseTruncatedMellinCoefficient_support_card {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] (E : ∀ i, Finset (ZMod (p i)))
    (t : ℝ) (K : ℕ) (χ : ∀ i, MulChar (ZMod (p i)) ℂ)
    (hc : sparseTruncatedMellinCoefficient p E t K χ ≠ 0) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => χ i ≠ 1)).card ≤ 2 * K := by
  unfold sparseTruncatedMellinCoefficient at hc
  obtain ⟨v, hv, hprod⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have hvK := (Finset.mem_filter.mp hv).2
  have hn (i : Fin n) := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ _)
  have hb (i : Fin n) : χ i ≠ 1 → (v i).1 = true ∨ (v i).2 = true := by
    intro hχ
    by_contra h
    have h₁ : (v i).1 = false := by cases hh : (v i).1 <;> simp_all
    have h₂ : (v i).2 = false := by cases hh : (v i).2 <;> simp_all
    have he : v i = (false, false) := Prod.ext h₁ h₂
    have hh := hn i
    simp only [he, sparsePatternMellin, hχ, ite_false, if_false, ne_eq, not_true_eq_false] at hh
  have hsum : ((Finset.univ : Finset (Fin n)).filter (fun i => χ i ≠ 1)).card ≤
      cubeDegree v false + cubeDegree v true := by
    rw [Finset.card_filter]
    unfold cubeDegree
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hχ : χ i = 1
    · simp [hχ]
    · have hh := hb i hχ
      rcases hh with hh | hh <;> simp [hχ, hh]
  omega

theorem sparse_coefficient_primitive_modulus_le {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (C L t : ℝ)
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ)
    (hc : sparseTruncatedMellinCoefficient p E t (sparseTruncationDegree C L) χ ≠ 0)
    (hlog : ∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L))
    (ρ : PrimitiveComplexCharacter)
    (hρ : primitiveCharacterReduction (sparseProductCharacter p χ) = some ρ) :
    ρ.modulus ≤ sparseConductorCutoff C L := by
  let S := (Finset.univ : Finset (Fin n)).filter (fun i => χ i ≠ 1)
  have hthrough := sparseProductCharacter_factorsThrough p χ S (by
    intro i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  apply (primitiveCharacterReduction_modulus_le _ hthrough ρ hρ).trans
  apply sparse_product_le_conductor_cutoff S p C L
  · intro i _
    exact (Fact.out : (p i).Prime).pos
  · intro i _
    exact hlog i
  · exact sparseTruncatedMellinCoefficient_support_card p E t _ χ hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_ElementaryPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The subset polynomial used in the nonnegative sparse weight -/

namespace Ostmann
open scoped Classical BigOperators

theorem elementaryCoefficient_polynomial {n : ℕ} (b : Fin n → ℂ) (u : ℂ) :
    finitePolynomial (elementaryCoefficient b) (n + 1) u = ∏ i, (1 + u * b i) := by
  unfold finitePolynomial elementaryCoefficient
  simp_rw [smul_eq_mul, Finset.mul_sum]
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        ∑ I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card = j),
          u ^ I.card * ∏ i ∈ I, b i := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro I hI
      rw [(Finset.mem_filter.mp hI).2]
    _ = ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset, u ^ I.card * ∏ i ∈ I, b i := by
      apply Finset.sum_fiberwise_of_maps_to
      intro I hI
      apply Finset.mem_range.mpr
      have hh := Finset.card_le_card (Finset.mem_powerset.mp hI)
      simpa only [Finset.card_univ, Fintype.card_fin] using Nat.lt_succ_of_le hh
    _ = _ := by
      rw [Finset.prod_one_add]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem elementaryCoefficient_product {n : ℕ} (b : Fin n → ℂ) (u v : ℂ) :
    finitePolynomial₂ (fun i j => elementaryCoefficient b i * elementaryCoefficient b j)
      (n + 1) u v = (∏ i, (1 + u * b i)) * ∏ i, (1 + v * b i) := by
  rw [← elementaryCoefficient_polynomial b u, ← elementaryCoefficient_polynomial b v]
  unfold finitePolynomial₂ finitePolynomial
  simp only [smul_eq_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem elementaryTruncation_eq {n : ℕ} (b : Fin n → ℂ) (K : ℕ) :
    (∑ i ∈ Finset.range (n + 1), if i ≤ K then elementaryCoefficient b i else 0) =
      elementaryTruncation b K := by
  rw [← Finset.sum_filter]
  unfold elementaryCoefficient elementaryTruncation
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext I
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_range]
    constructor
    · rintro ⟨hI, _, hK⟩
      exact ⟨hI, hK⟩
    · rintro ⟨hI, hK⟩
      have hh : I.card ≤ n := by simpa using Finset.card_le_card hI
      exact ⟨hI, Nat.lt_succ_of_le hh, hK⟩
  · intro I _
    rfl

theorem elementaryTruncation_square {n : ℕ} (b : Fin n → ℂ) (K : ℕ) :
    rectangularPolynomialSum (fun i j => elementaryCoefficient b i * elementaryCoefficient b j)
      (n + 1) K = elementaryTruncation b K ^ 2 := by
  rw [pow_two, ← elementaryTruncation_eq b K]
  unfold rectangularPolynomialSum
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : i ≤ K <;> by_cases hj : j ≤ K <;> simp [hi, hj]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_TruncatedBilinearCube
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact truncation of the two subset choices -/
namespace Ostmann
open scoped Classical BigOperators

theorem cubeCoefficient_truncation {n : ℕ} (A : BilinearCube n → ℂ) (K : ℕ) :
    rectangularPolynomialSum (cubeCoefficient A) (n + 1) K =
      ∑ v ∈ (Finset.univ : Finset (BilinearCube n)).filter
        (fun v => cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K), A v := by
  let B : BilinearCube n → ℂ := fun v =>
    if cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K then A v else 0
  have hc (j k : ℕ) : cubeCoefficient B j k =
      if j ≤ K ∧ k ≤ K then cubeCoefficient A j k else 0 := by
    unfold cubeCoefficient
    calc
      _ = ∑ v ∈ (Finset.univ : Finset (BilinearCube n)).filter
          (fun v => (cubeDegree v false, cubeDegree v true) = (j, k)),
          if j ≤ K ∧ k ≤ K then A v else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        have he := (Finset.mem_filter.mp hv).2
        have hj : cubeDegree v false = j := congrArg Prod.fst he
        have hk : cubeDegree v true = k := congrArg Prod.snd he
        dsimp only [B]
        simp only [hj, hk]
      _ = _ := by by_cases h : j ≤ K ∧ k ≤ K <;> simp [h]
  have hh := cubeCoefficient_polynomial B 1 1
  simp only [finitePolynomial₂, finitePolynomial, hc, one_pow, one_mul,
    smul_eq_mul] at hh
  simpa only [rectangularPolynomialSum, B, Finset.sum_filter] using hh

theorem subsetPair_cubeCoefficient {n : ℕ} (b : Fin n → ℂ)
    (j k : ℕ) (hj : j < n + 1) (hk : k < n + 1) :
    cubeCoefficient (fun v => ∏ i, subsetPairFactor (b i) (v i)) j k =
      elementaryCoefficient b j * elementaryCoefficient b k := by
  apply finitePolynomial₂_coefficient_unique (N := n + 1) _ _ _ j k hj hk
  intro u v
  rw [← bilinear_product_expansion, elementaryCoefficient_product, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [subsetPairFactor]
  ring

theorem elementaryTruncation_square_cube {n : ℕ} (b : Fin n → ℂ) (K : ℕ) :
    elementaryTruncation b K ^ 2 =
      ∑ v ∈ (Finset.univ : Finset (BilinearCube n)).filter
        (fun v => cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K),
          ∏ i, subsetPairFactor (b i) (v i) := by
  rw [← cubeCoefficient_truncation, ← elementaryTruncation_square]
  unfold rectangularPolynomialSum
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : j ≤ K ∧ k ≤ K
  · simp only [h]
    exact (subsetPair_cubeCoefficient b j k (Finset.mem_range.mp hj)
      (Finset.mem_range.mp hk)).symm
  · simp only [h, ite_false, if_false]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseWeightMellinExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicative Fourier expansion of the original squared subset weight -/
namespace Ostmann
open scoped Classical BigOperators

attribute [local instance] OAI.Ostmann.instFintypeMulCharZModComplexOfFactPrime_solutions_4
theorem sparsePatternMellin_inversion {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (t : ℝ) (v : Bool × Bool) (x : (ZMod p)ˣ) :
    subsetPairFactor (sparseAdditiveKernel E t x) v =
      ∑ χ : MulChar (ZMod p) ℂ, sparsePatternMellin E t χ v * χ x := by
  rcases v with ⟨v, w⟩
  cases v <;> cases w
  · simp only [subsetPairFactor, sparsePatternMellin, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, MulChar.one_apply_coe]
  · exact (mellin_inversion (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x) x).symm
  · exact (mellin_inversion (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x) x).symm
  · exact (mellin_inversion (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ 2) x).symm

theorem sparseWeight_mellin_expansion {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ)
    (x : ∀ i, (ZMod (p i))ˣ) :
    elementaryTruncation (fun i => sparseAdditiveKernel (E i) t (x i)) K ^ 2 =
      ∑ χ : (∀ i, MulChar (ZMod (p i)) ℂ),
        sparseTruncatedMellinCoefficient p E t K χ * ∏ i, χ i (x i) := by
  rw [elementaryTruncation_square_cube]
  simp_rw [sparsePatternMellin_inversion]
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  unfold sparseTruncatedMellinCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  exact Finset.prod_mul_distrib

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InjectiveCoefficientTransport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of coefficients along an injective character reduction -/
namespace Ostmann
open scoped Classical BigOperators

theorem injectiveCoefficient_apply {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (w : α → ℂ) (a : α) : injectiveCoefficient f w (f a) = w a := by
  unfold injectiveCoefficient
  rw [dite_eq_left ⟨a, rfl⟩]
  congr 1
  exact hf (Exists.choose_spec (show ∃ a', f a' = f a from ⟨a, rfl⟩))

theorem injectiveCoefficient_norm_le {α β : Type*} (f : α → β) (w : α → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hw : ∀ a, ‖w a‖ ≤ B) (b : β) :
    ‖injectiveCoefficient f w b‖ ≤ B := by
  unfold injectiveCoefficient
  split_ifs with h
  · exact hw h.choose
  · simpa only [norm_zero] using hB

theorem injectiveCoefficient_ne_zero {α β : Type*} (f : α → β) (w : α → ℂ)
    (b : β) (hb : injectiveCoefficient f w b ≠ 0) :
    ∃ a, f a = b ∧ w a ≠ 0 := by
  unfold injectiveCoefficient at hb
  split_ifs at hb with h
  · exact ⟨h.choose, h.choose_spec, hb⟩
  · exact (hb rfl).elim

theorem injectiveCoefficient_sum {α β : Type*} [Fintype α]
    (f : α → β) (hf : Function.Injective f) (w : α → ℂ) (g : β → ℂ) :
    (∑ b ∈ ((Finset.univ : Finset α).filter (fun a => w a ≠ 0)).image f,
      injectiveCoefficient f w b * g b) = ∑ a, w a * g (f a) := by
  rw [Finset.sum_image (fun a _ b _ h => hf h)]
  simp_rw [injectiveCoefficient_apply f hf w]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : w a = 0 <;> simp [h]

/-- Splitting a finite option family isolates the unique principal coefficient. -/
theorem sum_option_support {β : Type*} (S : Finset (Option β)) (h : Option β → ℂ)
    (hzero : none ∉ S → h none = 0) :
    (∑ e ∈ S, h e) = h none + ∑ b ∈ S.eraseNone, h (some b) := by
  have hs : (∑ b ∈ S.eraseNone, h (some b)) = ∑ e ∈ S.erase none, h e := by
    rw [← Finset.image_some_eraseNone S, Finset.sum_image
      (fun a _ b _ hab => Option.some.inj hab)]
  rw [hs]
  by_cases hn : none ∈ S
  · exact (Finset.add_sum_erase S h hn).symm
  · rw [Finset.erase_eq_of_notMem hn, hzero hn, zero_add]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePrimitiveExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sparse weight as a bounded sum of primitive characters -/
namespace Ostmann
open scoped Classical BigOperators

theorem sparsePrimitiveLabel_injective {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Function.Injective (sparsePrimitiveLabel p) :=
  (primitiveCharacterReduction_injective _).comp (sparseProductCharacter_injective p hc)

theorem sparsePrimitiveCoefficient_norm_le {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (hE : ∀ i, 0 ∉ E i)
    (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : ∀ i, (36 : ℝ) ≤ p i) (K : ℕ) (e : Option PrimitiveComplexCharacter) :
    ‖sparsePrimitiveCoefficient p E t K e‖ ≤ Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) :=
  injectiveCoefficient_norm_le _ _ _ (Real.exp_nonneg _)
    (sparseTruncatedMellinCoefficient_norm_le p E hE hsym t ht ht1 hp K) e

attribute [local instance] OAI.Ostmann.instFintypeMulCharZModComplexOfFactPrime_solutions_5
theorem sparsePrimitiveSupport_modulus_le {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (C L t : ℝ)
    (hlog : ∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L))
    (ρ : PrimitiveComplexCharacter)
    (hρ : ρ ∈ (sparsePrimitiveSupport p E t (sparseTruncationDegree C L)).eraseNone) :
    ρ.modulus ≤ sparseConductorCutoff C L := by
  obtain ⟨χ, hχ, he⟩ := Finset.mem_image.mp (Finset.mem_eraseNone.mp hρ)
  exact sparse_coefficient_primitive_modulus_le p E C L t χ (Finset.mem_filter.mp hχ).2 hlog ρ he

theorem sparseWeight_primitive_expansion {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) (u : (ZMod (∏ i, p i))ˣ) :
    elementaryTruncation
        (fun i => sparseAdditiveKernel (E i) t (crtUnitEquiv p hc u i)) K ^ 2 =
      sparsePrimitiveCoefficient p E t K none +
      ∑ ρ ∈ (sparsePrimitiveSupport p E t K).eraseNone,
        sparsePrimitiveCoefficient p E t K (some ρ) *
          liftPrimitiveCharacter (∏ i, p i) (some ρ) u := by
  let f := sparsePrimitiveLabel p
  let w := sparseTruncatedMellinCoefficient p E t K
  let g : Option PrimitiveComplexCharacter → ℂ := fun e => liftPrimitiveCharacter (∏ i, p i) e u
  have hf := sparsePrimitiveLabel_injective p hc
  have hsum := injectiveCoefficient_sum f hf w g
  have hsplit := sum_option_support (sparsePrimitiveSupport p E t K)
    (fun e => sparsePrimitiveCoefficient p E t K e * g e) (by
      intro he
      have hz : sparsePrimitiveCoefficient p E t K none = 0 := by
        by_contra hh
        obtain ⟨χ, hχ, hw⟩ := injectiveCoefficient_ne_zero f w none hh
        exact he (Finset.mem_image.mpr ⟨χ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, hχ⟩)
      rw [hz, zero_mul])
  have hlabel (χ : ∀ i, MulChar (ZMod (p i)) ℂ) :
      g (f χ) = sparseProductCharacter p χ u := by
    exact congrArg (fun z : DirichletCharacter ℂ (∏ i, p i) => z u)
      (lift_primitiveCharacterReduction (sparseProductCharacter p χ))
  calc
    _ = ∑ χ : (∀ i, MulChar (ZMod (p i)) ℂ), w χ * sparseProductCharacter p χ u := by
      rw [sparseWeight_mellin_expansion]
      apply Finset.sum_congr rfl
      intro χ _
      rw [sparseProductCharacter_apply p hc]
    _ = ∑ χ, w χ * g (f χ) := by simp only [hlabel]
    _ = ∑ e ∈ sparsePrimitiveSupport p E t K, sparsePrimitiveCoefficient p E t K e * g e :=
      by
        dsimp only [f, w, sparsePrimitiveSupport, sparsePrimitiveCoefficient] at hsum ⊢
        convert hsum.symm using 2
        all_goals try with_reducible_and_instances rfl
        ext e
        simp only [Finset.mem_image]
    _ = _ := by
      rw [hsplit]
      simp only [g, liftPrimitiveCharacter, MulChar.one_apply_coe, mul_one]

theorem sparsePrimitiveSupport_modulus_dvd {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ)
    (ρ : PrimitiveComplexCharacter)
    (hρ : ρ ∈ (sparsePrimitiveSupport p E t K).eraseNone) : ρ.modulus ∣ ∏ i, p i := by
  obtain ⟨χ, _, he⟩ := Finset.mem_image.mp (Finset.mem_eraseNone.mp hρ)
  rw [primitiveCharacterReduction_modulus (sparseProductCharacter p χ) ρ he]
  exact DirichletCharacter.conductor_dvd_level _

theorem sparsePrimitiveSupport_avoids {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ)
    (exception : Option PrimitiveComplexCharacter)
    (havoid : ∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) :
    ∀ ρ ∈ (sparsePrimitiveSupport p E t K).eraseNone, some ρ ≠ exception := by
  intro ρ hρ he
  exact havoid ρ he.symm (sparsePrimitiveSupport_modulus_dvd p E t K ρ hρ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseIntegerExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The primitive expansion on integers coprime to the selected primes -/
namespace Ostmann
open scoped Classical BigOperators

theorem liftPrimitiveCharacter_apply_nat (N a : ℕ) (ρ : PrimitiveComplexCharacter)
    (hd : ρ.modulus ∣ N) (ha : a.Coprime N) :
    liftPrimitiveCharacter N (some ρ) (a : ZMod N) = ρ.character (a : ZMod ρ.modulus) := by
  rw [liftPrimitiveCharacter, dite_eq_left hd]
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a N).mpr ha
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu, ZMod.cast_natCast hd]

theorem sparseWeight_integer_expansion {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K a : ℕ) (ha : a.Coprime (∏ i, p i)) :
    elementaryTruncation (fun i => sparseAdditiveKernel (E i) t (a : ZMod (p i))) K ^ 2 =
      sparsePrimitiveCoefficient p E t K none +
      ∑ ρ ∈ (sparsePrimitiveSupport p E t K).eraseNone,
        sparsePrimitiveCoefficient p E t K (some ρ) * ρ.character (a : ZMod ρ.modulus) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a (∏ i, p i)).mpr ha
  have hv (i : Fin n) : (crtUnitEquiv p hc u i : ZMod (p i)) = a := by
    rw [crtUnitEquiv_apply]
    change ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i))
      (ZMod (p i)) (u : ZMod (∏ i, p i)) = _
    rw [hu, map_natCast]
  have hh := sparseWeight_primitive_expansion p hc E t K u
  have hl : (fun i => sparseAdditiveKernel (E i) t (crtUnitEquiv p hc u i)) =
      (fun i => sparseAdditiveKernel (E i) t (a : ZMod (p i))) := by
    funext i
    rw [hv]
  rw [hl] at hh
  apply hh.trans
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [hu, liftPrimitiveCharacter_apply_nat _ _ ρ
    (sparsePrimitiveSupport_modulus_dvd p E t K ρ hρ) ha]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RetainedLowZeroDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform low-zero decay in the manuscript's conductor range -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem retained_low_zero_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (a D : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 101 ≤ Q →
      Real.log Q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ F : Finset PrimitiveComplexCharacter,
        (∀ χ ∈ F, χ.modulus ≤ Q) → (∀ χ ∈ F, some χ ≠ exception) →
        (∑ χ ∈ F, ∑ i ∈ ((Z χ).heightIndices ((Q : ℝ) ^ 5)).filter
          (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
            Real.exp (-Real.exp L * (1 - ((Z χ).zeros i).re))) ≤ Real.exp (-D * L) := by
  obtain ⟨C, c, _, hc, hzero⟩ := retained_low_zero_estimate Z hD hR
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul_left (84 * a)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventual_low_zero_error C c a D hc ha, hsmall,
    eventually_ge_atTop (1 : ℝ)] with L herr hsmall hL
  intro Q hQ hQL
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hQp : (0 : ℝ) < Q := by linarith
  have hT : (2 : ℝ) ≤ (Q : ℝ) ^ 5 := by
    calc
      2 ≤ (Q : ℝ) := by exact_mod_cast (show 2 ≤ Q by omega)
      _ ≤ (Q : ℝ) * (Q : ℝ) ^ 4 :=
        le_mul_of_one_le_right hQp.le (one_le_pow₀ hQr)
      _ = _ := by ring
  have hlogQT : Real.log ((Q : ℝ) * (Q : ℝ) ^ 5) = 6 * Real.log Q := by
    rw [Real.log_mul hQp.ne' (pow_ne_zero _ hQp.ne'), Real.log_pow]
    ring
  have hlogQ2T : Real.log ((Q : ℝ) ^ 2 * (Q : ℝ) ^ 5) = 7 * Real.log Q := by
    rw [Real.log_mul (pow_ne_zero _ hQp.ne') (pow_ne_zero _ hQp.ne'), Real.log_pow,
      Real.log_pow]
    ring
  have hlog2QT : Real.log (2 * (Q : ℝ) * (Q : ℝ) ^ 5) =
      Real.log 2 + 6 * Real.log Q := by
    rw [Real.log_mul (mul_ne_zero (by norm_num) hQp.ne') (pow_ne_zero _ hQp.ne'),
      Real.log_mul (by norm_num) hQp.ne', Real.log_pow]
    ring
  have hg : 84 * a * L ≤ Real.exp ((1 / 10 : ℝ) * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 84 * a * L),
      abs_of_pos (Real.exp_pos _), one_mul] using hsmall
  have hM : 12 * Real.log ((Q : ℝ) ^ 2 * (Q : ℝ) ^ 5) ≤ Real.exp L := by
    rw [hlogQ2T]
    have hm := mul_le_mul_of_nonneg_right hg (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    have he : Real.exp ((1 / 10 : ℝ) * L) * Real.exp ((9 / 10 : ℝ) * L) =
        Real.exp L := by rw [← Real.exp_add]; congr 1; ring
    rw [he] at hm
    linarith
  obtain ⟨exception, he⟩ := hzero Q hQ ((Q : ℝ) ^ 5) hT
  refine ⟨exception, ?_⟩
  intro F hF hFE
  have hh := he F hF hFE (Real.exp L) hM
  rw [hlogQT, hlog2QT] at hh
  exact hh.trans (herr (Real.log Q) (Real.log_nonneg hQr) hQL)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothZeroTermBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit-formula zero terms and their high-ordinate tail -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothZeroTerm_norm_bound {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (χ : PrimitiveComplexCharacter)
    (X : ℝ) (i : ℕ) :
    ‖smoothZeroTerm Z χ X i‖ ≤
      Real.exp (((Z χ).zeros i).re * Real.log X) * P.mellinConstant *
        Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) := by
  have hs := (Z χ).in_strip i
  have hm := P.mellin_decay ((Z χ).zeros i) (by linarith) (by linarith)
  rw [smoothZeroTerm, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)).trans_eq (by ring)

theorem selected_zero_height_count {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (Q : ℕ) (hQ : 1 ≤ Q)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q)
    (S : Finset (Σ _χ : PrimitiveComplexCharacter, ℕ))
    (hS : ∀ z ∈ S, z.1 ∈ F) (T : ℝ) (hT : 0 ≤ T) :
    ((S.filter (fun z => |((Z z.1).zeros z.2).im| ≤ T)).card : ℝ) ≤
      (P.zeroCountConstant * (Q : ℝ) ^ 2) * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := by
  have hsub : S.filter (fun z => |((Z z.1).zeros z.2).im| ≤ T) ⊆
      F.sigma (fun χ => (Z χ).heightIndices T) := by
    intro z hz
    obtain ⟨hzS, ht⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_sigma.mpr ⟨hS z hzS, ((Z z.1).mem_heightIndices T z.2).mpr ht⟩
  have hcard (χ : PrimitiveComplexCharacter) :
      ((Z χ).heightIndices T).card = (Z χ).count 0 T := by
    unfold ComplexZeroEnumeration.count
    rw [Finset.filter_eq_self.mpr (fun i _ => ((Z χ).in_strip i).1.le)]
  calc
    _ ≤ ((F.sigma (fun χ => (Z χ).heightIndices T)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = ∑ χ ∈ F, ((Z χ).count 0 T : ℝ) := by
      rw [Finset.card_sigma, Nat.cast_sum]
      simp only [hcard]
    _ ≤ _ := P.zero_count Q hQ T hT F hF

theorem finite_high_smooth_zero_bound {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (Q : ℕ) (hQ : 1 ≤ Q)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q)
    (S : Finset (Σ _χ : PrimitiveComplexCharacter, ℕ))
    (hS : ∀ z ∈ S, z.1 ∈ F) (T X : ℝ) (hT : 0 ≤ T) (hX : 1 ≤ X)
    (hheight : ∀ z ∈ S, T ≤ |((Z z.1).zeros z.2).im|) :
    (∑ z ∈ S, ‖smoothZeroTerm Z z.1 X z.2‖) ≤
      (X * P.mellinConstant) *
        (2 * (2 * (P.zeroCountConstant * (Q : ℝ) ^ 2) * (Real.log Q + 3)) ^ 2 *
          Real.exp (-4 * Real.log (1 + T))) := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hX0 : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hpoint (z) (hz : z ∈ S) :
      ‖smoothZeroTerm Z z.1 X z.2‖ ≤ (X * P.mellinConstant) *
        Real.exp (-8 * Real.log (1 + |((Z z.1).zeros z.2).im|)) := by
    apply (smoothZeroTerm_norm_bound P z.1 X z.2).trans
    have he : Real.exp (((Z z.1).zeros z.2).re * Real.log X) ≤ X := by
      calc
        _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right ((Z z.1).in_strip z.2).2.le hlogX)
        _ = X := Real.exp_log hX0
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right he P.mellinConstant_pos.le) (Real.exp_nonneg _)
  have htail := finite_high_zero_tail_bound S (fun z => |((Z z.1).zeros z.2).im|)
    (Q : ℝ) (P.zeroCountConstant * (Q : ℝ) ^ 2) T hQr
    (mul_nonneg P.zeroCountConstant_pos.le (sq_nonneg _)) hT hheight
    (selected_zero_height_count P Q hQ F hF S hS)
  calc
    _ ≤ ∑ z ∈ S, (X * P.mellinConstant) *
        Real.exp (-8 * Real.log (1 + |((Z z.1).zeros z.2).im|)) :=
      Finset.sum_le_sum hpoint
    _ = (X * P.mellinConstant) *
        ∑ z ∈ S, Real.exp (-8 * Real.log (1 + |((Z z.1).zeros z.2).im|)) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (mul_nonneg hX0.le P.mellinConstant_pos.le)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_InfiniteHighZeroBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete high-zero tail over a finite character family -/

namespace Ostmann
open scoped Classical BigOperators

theorem high_smooth_zero_tsum_bound {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (Q : ℕ) (hQ : 1 ≤ Q)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q)
    (T X : ℝ) (hT : 0 ≤ T) (hX : 1 ≤ X) :
    (∑ χ ∈ F, ∑' i : ℕ, if T ≤ |((Z χ).zeros i).im| then
      ‖smoothZeroTerm Z χ X i‖ else 0) ≤
      (X * P.mellinConstant) *
        (2 * (2 * (P.zeroCountConstant * (Q : ℝ) ^ 2) * (Real.log Q + 3)) ^ 2 *
          Real.exp (-4 * Real.log (1 + T))) := by
  let f : (Σ _χ : PrimitiveComplexCharacter, ℕ) → ℝ := fun z =>
    if z.1 ∈ F ∧ T ≤ |((Z z.1).zeros z.2).im| then ‖smoothZeroTerm Z z.1 X z.2‖ else 0
  have hf : 0 ≤ f := by intro z; dsimp [f]; split_ifs <;> positivity
  have hb (S : Finset (Σ _χ : PrimitiveComplexCharacter, ℕ)) :
      (∑ z ∈ S, f z) ≤
        (X * P.mellinConstant) *
          (2 * (2 * (P.zeroCountConstant * (Q : ℝ) ^ 2) * (Real.log Q + 3)) ^ 2 *
            Real.exp (-4 * Real.log (1 + T))) := by
    let G := S.filter (fun z => z.1 ∈ F ∧ T ≤ |((Z z.1).zeros z.2).im|)
    have he : (∑ z ∈ S, f z) = ∑ z ∈ G, ‖smoothZeroTerm Z z.1 X z.2‖ := by
      simp only [G, Finset.sum_filter, f]
    rw [he]
    exact finite_high_smooth_zero_bound P Q hQ F hF G
      (fun z hz => (Finset.mem_filter.mp hz).2.1) T X hT hX
      (fun z hz => (Finset.mem_filter.mp hz).2.2)
  have hsum := summable_of_sum_le hf hb
  have hbound := Real.tsum_le_of_sum_le hf hb
  rw [hsum.tsum_sigma] at hbound
  have houter : (∑' χ, ∑' i, f ⟨χ, i⟩) = ∑ χ ∈ F, ∑' i, f ⟨χ, i⟩ := by
    apply tsum_eq_sum
    intro χ hχ
    simp only [f, hχ, false_and, ite_false, if_false, tsum_zero]
  rw [houter] at hbound
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro χ hχ
  apply tsum_congr
  intro i
  simp only [f, hχ, true_and]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothZeroSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating bounded-height and high-ordinate terms of the explicit formula -/

namespace Ostmann
open scoped Classical BigOperators

theorem nonnegative_tsum_finite_tail_bound {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hs : Summable f) (S : Finset ι) (P : ι → Prop)
    [DecidablePred P] (hcover : ∀ i ∉ S, P i) :
    (∑' i, f i) ≤ (∑ i ∈ S, f i) + ∑' i, if P i then f i else 0 := by
  let g := fun i => if i ∈ S then f i else 0
  let h := fun i => if P i then f i else 0
  have hg0 (i) : 0 ≤ g i := by dsimp [g]; split_ifs <;> simp_all
  have hh0 (i) : 0 ≤ h i := by dsimp [h]; split_ifs <;> simp_all
  have hg : Summable g := Summable.of_nonneg_of_le hg0
    (fun i => by dsimp [g]; split_ifs <;> simp_all) hs
  have hh : Summable h := Summable.of_nonneg_of_le hh0
    (fun i => by dsimp [h]; split_ifs <;> simp_all) hs
  have hpoint (i) : f i ≤ g i + h i := by
    by_cases hi : i ∈ S
    · simp only [g, hi, ite_true, if_true]
      exact le_add_of_nonneg_right (hh0 i)
    · simp only [g, hi, ite_false, if_false, zero_add, h, hcover i hi, ite_true, if_true, le_refl]
  have hsumg : (∑' i, g i) = ∑ i ∈ S, f i := by
    rw [tsum_eq_sum (s := S) (fun i hi => by simp [g, hi])]
    apply Finset.sum_congr rfl
    intro i hi
    simp [g, hi]
  have hbound := hs.tsum_le_tsum hpoint (hg.add hh)
  rw [hg.tsum_add hh, hsumg] at hbound
  exact hbound

theorem smoothZeroTerm_norm_coarse {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (χ : PrimitiveComplexCharacter) (X : ℝ) (i : ℕ) :
    ‖smoothZeroTerm Z χ X i‖ ≤
      Real.exp (((Z χ).zeros i).re * Real.log X) * P.mellinConstant := by
  have hlog : 0 ≤ Real.log (1 + |((Z χ).zeros i).im|) :=
    Real.log_nonneg (by linarith [abs_nonneg ((Z χ).zeros i).im])
  have he : Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  exact (smoothZeroTerm_norm_bound P χ X i).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he
      (mul_nonneg (Real.exp_nonneg _) P.mellinConstant_pos.le))

theorem bounded_height_zero_norm_sum {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (χ : PrimitiveComplexCharacter)
    (T X : ℝ) (hX : 1 ≤ X) :
    (∑ i ∈ (Z χ).heightIndices T, ‖smoothZeroTerm Z χ X i‖) ≤
      (X * P.mellinConstant) *
        (∑ i ∈ ((Z χ).heightIndices T).filter (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
          Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re))) +
      (Real.exp ((1 / 2 : ℝ) * Real.log X) * P.mellinConstant) *
        ((Z χ).heightIndices T).card := by
  have hXp : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hpoint (i : ℕ) : ‖smoothZeroTerm Z χ X i‖ ≤
      (if 1 / 2 ≤ ((Z χ).zeros i).re then
        X * P.mellinConstant * Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re)) else 0) +
      Real.exp ((1 / 2 : ℝ) * Real.log X) * P.mellinConstant := by
    by_cases hi : 1 / 2 ≤ ((Z χ).zeros i).re
    · simp only [hi, ite_true, if_true]
      have he : Real.exp (((Z χ).zeros i).re * Real.log X) =
          X * Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re)) := by
        calc
          _ = Real.exp (Real.log X + (-Real.log X * (1 - ((Z χ).zeros i).re))) := by
            congr 1
            ring
          _ = Real.exp (Real.log X) * Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re)) :=
            Real.exp_add _ _
          _ = _ := by rw [Real.exp_log hXp]
      have hh := smoothZeroTerm_norm_coarse P χ X i
      rw [he] at hh
      have hh' : ‖smoothZeroTerm Z χ X i‖ ≤
          X * P.mellinConstant * Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re)) := by
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        ring
      exact hh'.trans (le_add_of_nonneg_right (mul_nonneg (Real.exp_nonneg _) P.mellinConstant_pos.le))
    · simp only [hi, ite_false, if_false, zero_add]
      apply (smoothZeroTerm_norm_coarse P χ X i).trans
      apply mul_le_mul_of_nonneg_right _ P.mellinConstant_pos.le
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_of_not_ge hi) hlogX)
  have hh := Finset.sum_le_sum (s := (Z χ).heightIndices T) (fun i _ => hpoint i)
  rw [Finset.sum_add_distrib] at hh
  simpa only [← Finset.sum_filter, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    mul_comm (((Z χ).heightIndices T).card : ℝ), mul_assoc] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothCharacterFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth character mean with all zero contributions displayed -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothTrivialZeroTerm_norm_le {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (χ : PrimitiveComplexCharacter) :
    ‖smoothTrivialZeroTerm χ‖ ≤ P.mellinConstant := by
  have hh := P.mellin_decay 0 (by norm_num) (by norm_num)
  simp only [Complex.zero_im, abs_zero, add_zero, Real.log_one, mul_zero,
    Real.exp_zero, mul_one] at hh
  unfold smoothTrivialZeroTerm
  split_ifs
  · exact hh
  · simpa only [norm_zero] using P.mellinConstant_pos.le

theorem smooth_character_bounded_height {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (χ : PrimitiveComplexCharacter)
    (X T : ℝ) (hX : 2 ≤ X) :
    ‖smoothMangoldtMean χ.modulus χ.character X‖ ≤
      (∑ i ∈ (Z χ).heightIndices T, ‖smoothZeroTerm Z χ X i‖) +
      (∑' i, if T ≤ |((Z χ).zeros i).im| then ‖smoothZeroTerm Z χ X i‖ else 0) +
      P.mellinConstant + P.errorConstant / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ)) := by
  have htri : ‖smoothMangoldtMean χ.modulus χ.character X‖ ≤
      ‖smoothMangoldtMean χ.modulus χ.character X +
        (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ‖ +
        ‖∑' i, smoothZeroTerm Z χ X i‖ + ‖smoothTrivialZeroTerm χ‖ := by
    have he : smoothMangoldtMean χ.modulus χ.character X =
        (smoothMangoldtMean χ.modulus χ.character X +
          (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ) -
          (∑' i, smoothZeroTerm Z χ X i) - smoothTrivialZeroTerm χ := by ring
    calc
      _ = ‖(smoothMangoldtMean χ.modulus χ.character X +
          (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ) -
          (∑' i, smoothZeroTerm Z χ X i) - smoothTrivialZeroTerm χ‖ := congrArg norm he
      _ ≤ _ := (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  have hn := norm_tsum_le_tsum_norm (P.absolute_summability χ X hX)
  have hz := nonnegative_tsum_finite_tail_bound (fun i => ‖smoothZeroTerm Z χ X i‖)
    (fun _ => norm_nonneg _) (P.absolute_summability χ X hX) ((Z χ).heightIndices T)
    (fun i => T ≤ |((Z χ).zeros i).im|) (fun i hi => by
      have hh : ¬ |((Z χ).zeros i).im| ≤ T := by
        simpa only [ComplexZeroEnumeration.mem_heightIndices] using hi
      exact (lt_of_not_ge hh).le)
  linarith [P.explicit_formula χ X hX, smoothTrivialZeroTerm_norm_le P χ]

theorem smooth_nonprincipal_family_bound {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (Q : ℕ) (hQ : 1 ≤ Q)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q)
    (T X : ℝ) (hT : 0 ≤ T) (hX : 2 ≤ X) :
    (∑ χ ∈ F, ‖smoothMangoldtMean χ.modulus χ.character X‖) ≤
      (X * P.mellinConstant) *
        (∑ χ ∈ F, ∑ i ∈ ((Z χ).heightIndices T).filter
          (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
            Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re))) +
      (Real.exp ((1 / 2 : ℝ) * Real.log X) * P.mellinConstant) *
        (P.zeroCountConstant * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2))) +
      (X * P.mellinConstant) *
        (2 * (2 * (P.zeroCountConstant * (Q : ℝ) ^ 2) * (Real.log Q + 3)) ^ 2 *
          Real.exp (-4 * Real.log (1 + T))) +
      (F.card : ℝ) * (P.mellinConstant + P.errorConstant / Real.sqrt X * Real.log (2 * (Q : ℝ))) := by
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hX1 : 1 ≤ X := by linarith
  have hpoint (χ) (hχ : χ ∈ F) :
      ‖smoothMangoldtMean χ.modulus χ.character X‖ ≤
      (X * P.mellinConstant) *
        (∑ i ∈ ((Z χ).heightIndices T).filter (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
          Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re))) +
      (Real.exp ((1 / 2 : ℝ) * Real.log X) * P.mellinConstant) *
        ((Z χ).heightIndices T).card +
      (∑' i, if T ≤ |((Z χ).zeros i).im| then ‖smoothZeroTerm Z χ X i‖ else 0) +
      (P.mellinConstant + P.errorConstant / Real.sqrt X * Real.log (2 * (Q : ℝ))) := by
    have ht := smooth_character_bounded_height P χ X T hX
    have hz := bounded_height_zero_norm_sum P χ T X hX1
    have hlog : Real.log (2 * (χ.modulus : ℝ)) ≤ Real.log (2 * (Q : ℝ)) := by
      apply Real.log_le_log (by have hp := χ.positive; positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hF χ hχ) (by norm_num)
    have he := mul_le_mul_of_nonneg_left hlog
      (div_nonneg P.errorConstant_pos.le (Real.sqrt_nonneg X))
    linarith
  have hh := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hh
  have hc : (∑ χ ∈ F, (((Z χ).heightIndices T).card : ℝ)) ≤
      P.zeroCountConstant * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := by
    have he (χ : PrimitiveComplexCharacter) : ((Z χ).heightIndices T).card =
        (Z χ).count 0 T := by
      unfold ComplexZeroEnumeration.count
      rw [Finset.filter_eq_self.mpr (fun i _ => ((Z χ).in_strip i).1.le)]
    simp only [he]
    exact P.zero_count Q hQ T hT F hF
  have hc' := mul_le_mul_of_nonneg_left hc
    (mul_nonneg (Real.exp_nonneg ((1 / 2 : ℝ) * Real.log X)) P.mellinConstant_pos.le)
  have hhigh := high_smooth_zero_tsum_bound P Q hQ F hF T X hT hX1
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothFamilyEnvelopes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary exponential envelopes for the non-low-zero errors -/
namespace Ostmann
open scoped Classical BigOperators

private theorem exponential_split (X t : ℝ) (hX : 0 < X) :
    X * Real.exp (t - Real.log X / 2) = Real.exp (Real.log X / 2 + t) := by
  calc
    _ = Real.exp (Real.log X) * Real.exp (t - Real.log X / 2) := by
      rw [Real.exp_log hX]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

private theorem log_height_bound (Q : ℝ) (hQ : 1 ≤ Q) :
    Real.log (Q * (Q ^ 5 + 2)) ≤ 8 * Q := by
  have hp : 0 < Q := by linarith
  have hpow : 1 ≤ Q ^ 5 := one_le_pow₀ hQ
  calc
    _ ≤ Real.log (3 * Q ^ 6) := by
      apply Real.log_le_log (by positivity)
      nlinarith
    _ = Real.log 3 + 6 * Real.log Q := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hp.ne'), Real.log_pow]
      norm_num
    _ ≤ 8 * Q := by
      have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      have hh := Real.log_le_self hp.le
      linarith

/-- The zeros with real part below one half. -/
theorem smooth_middle_zero_envelope (Cm Cz Q X : ℝ)
    (hm : 0 ≤ Cm) (hz : 0 ≤ Cz) (hQ : 1 ≤ Q) (hX : 0 < X) :
    (Real.exp ((1 / 2 : ℝ) * Real.log X) * Cm) *
      (Cz * Q ^ 2 * (Q ^ 5 + 1) * Real.log (Q * (Q ^ 5 + 2))) ≤
      X * ((16 * Cm * Cz) * Real.exp (8 * Real.log Q - Real.log X / 2)) := by
  have hp : 0 < Q := by linarith
  have hp5 : 1 ≤ Q ^ 5 := one_le_pow₀ hQ
  have he : Q ^ 8 = Real.exp (8 * Real.log Q) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hp] using (Real.exp_nat_mul (Real.log Q) 8).symm
  calc
    _ ≤ (Real.exp ((1 / 2 : ℝ) * Real.log X) * Cm) *
        (Cz * Q ^ 2 * (2 * Q ^ 5) * (8 * Q)) := by
      have hl : 0 ≤ Real.log (Q * (Q ^ 5 + 2)) :=
        Real.log_nonneg (by nlinarith)
      gcongr
      · linarith
      · exact log_height_bound Q hQ
    _ = (16 * Cm * Cz) * (Real.exp ((1 / 2 : ℝ) * Real.log X) * Q ^ 8) := by ring
    _ = _ := by
      rw [he, ← Real.exp_add]
      calc
        _ = (16 * Cm * Cz) * (X * Real.exp (8 * Real.log Q - Real.log X / 2)) := by
          rw [exponential_split X _ hX]
          congr 2
          ring
        _ = _ := by ring

/-- The complete high-ordinate tail, including all its zeros. -/
theorem smooth_high_zero_envelope (Cm Cz Q X : ℝ)
    (hm : 0 ≤ Cm) (hz : 0 ≤ Cz) (hQ : 1 ≤ Q) (hX : 0 ≤ X) :
    (X * Cm) * (2 * (2 * (Cz * Q ^ 2) * (Real.log Q + 3)) ^ 2 *
      Real.exp (-4 * Real.log (1 + Q ^ 5))) ≤
      X * ((128 * Cm * Cz ^ 2) * Real.exp (-Real.log Q)) := by
  have hp : 0 < Q := by linarith
  have hl0 := Real.log_nonneg hQ
  have hl : Real.log Q + 3 ≤ 4 * Q := by
    have hh := Real.log_le_self hp.le
    linarith
  have htail : Real.exp (-4 * Real.log (1 + Q ^ 5)) ≤
      Real.exp (-20 * Real.log Q) := by
    apply Real.exp_le_exp.mpr
    have hh := Real.log_le_log (pow_pos hp 5) (show Q ^ 5 ≤ 1 + Q ^ 5 by linarith)
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hpow : Q ^ 6 = Real.exp (6 * Real.log Q) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hp] using (Real.exp_nat_mul (Real.log Q) 6).symm
  calc
    _ ≤ (X * Cm) * (2 * (2 * (Cz * Q ^ 2) * (4 * Q)) ^ 2 *
        Real.exp (-20 * Real.log Q)) := by
      gcongr
    _ = X * ((128 * Cm * Cz ^ 2) *
        (Q ^ 6 * Real.exp (-20 * Real.log Q))) := by ring
    _ = X * ((128 * Cm * Cz ^ 2) * Real.exp (-14 * Real.log Q)) := by
      rw [hpow, ← Real.exp_add]
      congr 3
      ring
    _ ≤ _ := by gcongr; linarith

/-- The trivial-zero and shifted-contour remainders, summed over the family. -/
theorem smooth_family_remainder_envelope (Cm E Q X : ℝ) (N : ℕ)
    (hm : 0 ≤ Cm) (hE : 0 ≤ E) (hQ : 1 ≤ Q) (hX : 1 ≤ X)
    (hN : (N : ℝ) ≤ Q ^ 2) :
    (N : ℝ) * (Cm + E / Real.sqrt X * Real.log (2 * Q)) ≤
      X * ((Cm + 2 * E) * Real.exp (3 * Real.log Q - Real.log X / 2)) := by
  have hp : 0 < Q := by linarith
  have hXp : 0 < X := by linarith
  have hs : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa)
  have hi : E / Real.sqrt X ≤ E := (div_le_self hE hs)
  have hl0 : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
  have hl : Real.log (2 * Q) ≤ 2 * Q := Real.log_le_self (by positivity)
  have hpow : Q ^ 3 = Real.exp (3 * Real.log Q) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hp] using (Real.exp_nat_mul (Real.log Q) 3).symm
  have hexp : 1 ≤ Real.exp (Real.log X / 2) :=
    Real.one_le_exp (by have hh := Real.log_nonneg hX; linarith)
  calc
    _ ≤ Q ^ 2 * (Cm + E * (2 * Q)) := by gcongr
    _ ≤ (Cm + 2 * E) * Q ^ 3 := by
      have hh := mul_le_mul_of_nonneg_left hQ (mul_nonneg hm (sq_nonneg Q))
      nlinarith
    _ ≤ (Cm + 2 * E) * (Real.exp (Real.log X / 2) * Q ^ 3) := by
      gcongr
      exact le_mul_of_one_le_left (by positivity) hexp
    _ = _ := by
      rw [hpow, ← Real.exp_add]
      calc
        _ = (Cm + 2 * E) * (X * Real.exp (3 * Real.log Q - Real.log X / 2)) := by
          rw [exponential_split X _ hXp]
        _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothNonprincipalDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonprincipal part of manuscript Lemma 5.3

This is derived from the three precisely recorded analytic inputs.  The
exception is one entire primitive character, uniformly for every finite family.
-/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem smooth_nonprincipal_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (a D : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 101 ≤ Q →
      L ^ 2 ≤ Real.log Q → Real.log Q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ F : Finset PrimitiveComplexCharacter,
        (∀ χ ∈ F, χ.modulus ≤ Q) → (∀ χ ∈ F, some χ ≠ exception) →
        (∑ χ ∈ F, ‖smoothMangoldtMean χ.modulus χ.character (Real.exp (Real.exp L))‖) ≤
          Real.exp (Real.exp L) * Real.exp (-D * L) := by
  have hm := P.mellinConstant_pos.le
  have hz := P.zeroCountConstant_pos.le
  have he := P.errorConstant_pos.le
  filter_upwards [retained_low_zero_decay Z hD hR a (D + 1) ha,
    eventual_conductor_exponential_decay a 8 (16 * P.mellinConstant * P.zeroCountConstant)
      (D + 1) ha (by norm_num),
    eventual_conductor_negative_decay (128 * P.mellinConstant * P.zeroCountConstant ^ 2) (D + 1),
    eventual_conductor_exponential_decay a 3 (P.mellinConstant + 2 * P.errorConstant)
      (D + 1) ha (by norm_num),
    Real.tendsto_exp_atTop.eventually_ge_atTop (P.mellinConstant + 3),
    eventually_ge_atTop (1 : ℝ)] with L hlow hmid hhigh hrem hcoef hL
  intro Q hQ hQL hQU
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hq : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hX1 : 1 ≤ Real.exp (Real.exp L) := Real.one_le_exp (Real.exp_nonneg _)
  have hX2 : 2 ≤ Real.exp (Real.exp L) := by
    have hh := Real.add_one_le_exp (Real.exp L)
    have hh' : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
    linarith
  obtain ⟨exception, hlow⟩ := hlow Q hQ hQU
  refine ⟨exception, ?_⟩
  intro F hF hFE
  have hmain := smooth_nonprincipal_family_bound P Q (by omega) F hF
    ((Q : ℝ) ^ 5) (Real.exp (Real.exp L)) (by positivity) hX2
  have hl := hlow F hF hFE
  have hl' := mul_le_mul_of_nonneg_left hl
    (mul_nonneg (Real.exp_nonneg (Real.exp L)) hm)
  have hmid0 := smooth_middle_zero_envelope P.mellinConstant P.zeroCountConstant
    (Q : ℝ) (Real.exp (Real.exp L)) hm hz hQ1 (Real.exp_pos _)
  have hhigh0 := smooth_high_zero_envelope P.mellinConstant P.zeroCountConstant
    (Q : ℝ) (Real.exp (Real.exp L)) hm hz hQ1 (Real.exp_nonneg _)
  have hrem0 := smooth_family_remainder_envelope P.mellinConstant P.errorConstant
    (Q : ℝ) (Real.exp (Real.exp L)) F.card hm he hQ1 hX1
    (by exact_mod_cast primitive_character_family_card F Q hF)
  simp only [Real.log_exp] at hmain hmid0 hrem0
  have hmid1 := mul_le_mul_of_nonneg_left (hmid (Real.log Q) hq hQU)
    (Real.exp_nonneg (Real.exp L))
  have hhigh1 := mul_le_mul_of_nonneg_left (hhigh (Real.log Q) hQL)
    (Real.exp_nonneg (Real.exp L))
  have hrem1 := mul_le_mul_of_nonneg_left (hrem (Real.log Q) hq hQU)
    (Real.exp_nonneg (Real.exp L))
  have hsum : (∑ χ ∈ F, ‖smoothMangoldtMean χ.modulus χ.character
      (Real.exp (Real.exp L))‖) ≤ Real.exp (Real.exp L) *
        ((P.mellinConstant + 3) * Real.exp (-(D + 1) * L)) := by
    nlinarith [hmain, hl', hmid0, hmid1, hhigh0, hhigh1, hrem0, hrem1]
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  calc
    _ ≤ Real.exp L * Real.exp (-(D + 1) * L) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothPrincipalMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The principal term of the smooth character estimate

Published input: the conductor-one case of Montgomery–Vaughan (2007),
Corollary 11.20, equations (11.32)/(11.34), p.381, with the usual smooth
partial summation. This is the classical prime number theorem with its
zero-free-region error, specialized to our single fixed compactly supported
smooth function. It makes no assertion about a growing character family.
-/
namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators

theorem smooth_principal_decay (hPNT : PublishedSmoothPrincipalPNT) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, smoothPrincipalError (Real.exp (Real.exp L)) ≤
      Real.exp (Real.exp L) * Real.exp (-D * L) := by
  obtain ⟨C, c, _, hc, hPNT⟩ := hPNT
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul_left |D + 1|).bound hc
  filter_upwards [hsmall, Real.tendsto_exp_atTop.eventually_ge_atTop C,
    eventually_ge_atTop (1 : ℝ)] with L hs hC hL
  have hL0 : 0 ≤ L := by linarith
  have hX : 2 ≤ Real.exp (Real.exp L) := by
    have hh := Real.add_one_le_exp (Real.exp L)
    have hh' := Real.one_le_exp hL0
    linarith
  have hs' : |D + 1| * L ≤ c * Real.exp (L / 2) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hL0),
      abs_of_pos (Real.exp_pos _), show (1 / 2 : ℝ) * L = L / 2 by ring] using hs
  have hr : C * Real.exp (-c * Real.sqrt (Real.log (Real.exp (Real.exp L)))) ≤
      Real.exp (-D * L) := by
    rw [Real.log_exp, ← Real.exp_half]
    calc
      _ ≤ Real.exp L * Real.exp (-c * Real.exp (L / 2)) :=
        mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)
      _ = Real.exp (L - c * Real.exp (L / 2)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_right (le_abs_self (D + 1)) hL0
        linarith)
  calc
    _ ≤ C * Real.exp (Real.exp L) *
        Real.exp (-c * Real.sqrt (Real.log (Real.exp (Real.exp L)))) := hPNT _ hX
    _ = Real.exp (Real.exp L) *
        (C * Real.exp (-c * Real.sqrt (Real.log (Real.exp (Real.exp L))))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)

/-- Lemma 5.3, including the conductor-one term. -/
theorem smooth_primitive_family_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (hPNT : PublishedSmoothPrincipalPNT)
    (a D : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 101 ≤ Q →
      L ^ 2 ≤ Real.log Q → Real.log Q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ F : Finset PrimitiveComplexCharacter,
        (∀ χ ∈ F, χ.modulus ≤ Q) → (∀ χ ∈ F, some χ ≠ exception) →
        smoothPrincipalError (Real.exp (Real.exp L)) +
          (∑ χ ∈ F, ‖smoothMangoldtMean χ.modulus χ.character (Real.exp (Real.exp L))‖) ≤
          Real.exp (Real.exp L) * Real.exp (-D * L) := by
  filter_upwards [smooth_nonprincipal_decay Z hD hR P a (D + 1) ha,
    smooth_principal_decay hPNT (D + 1), eventually_ge_atTop (1 : ℝ)] with L hn hp hL
  intro Q hQ hl hu
  obtain ⟨exception, hn⟩ := hn Q hQ hl hu
  refine ⟨exception, ?_⟩
  intro F hF he
  have htwo : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  calc
    _ ≤ Real.exp (Real.exp L) * (2 * Real.exp (-(D + 1) * L)) := by
      linarith [hn F hF he]
    _ ≤ Real.exp (Real.exp L) * (Real.exp L * Real.exp (-(D + 1) * L)) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_WeightedSmoothCharacterMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted smooth character means at the actual truncation cutoff -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- A finite coefficient bound costs no factor equal to the number of characters. -/
theorem weighted_smooth_character_error (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (B X : ℝ)
    (hc₀ : ‖c₀‖ ≤ B) (hc : ∀ χ ∈ F, ‖c χ‖ ≤ B) :
    ‖c₀ * smoothMangoldtMean 1 1 X +
        ∑ χ ∈ F, c χ * smoothMangoldtMean χ.modulus χ.character X -
        c₀ * smoothPrincipalMain X‖ ≤
      B * (smoothPrincipalError X +
        ∑ χ ∈ F, ‖smoothMangoldtMean χ.modulus χ.character X‖) := by
  have he : c₀ * smoothMangoldtMean 1 1 X +
      ∑ χ ∈ F, c χ * smoothMangoldtMean χ.modulus χ.character X -
      c₀ * smoothPrincipalMain X =
      c₀ * (smoothMangoldtMean 1 1 X - smoothPrincipalMain X) +
      ∑ χ ∈ F, c χ * smoothMangoldtMean χ.modulus χ.character X := by ring
  rw [he]
  calc
    _ ≤ ‖c₀ * (smoothMangoldtMean 1 1 X - smoothPrincipalMain X)‖ +
        ∑ χ ∈ F, ‖c χ * smoothMangoldtMean χ.modulus χ.character X‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ B * smoothPrincipalError X +
        ∑ χ ∈ F, B * ‖smoothMangoldtMean χ.modulus χ.character X‖ := by
      simp only [norm_mul, smoothPrincipalError]
      gcongr
      exact hc _ (by assumption)
    _ = _ := by rw [← Finset.mul_sum, mul_add]

theorem weighted_sparse_character_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (hPNT : PublishedSmoothPrincipalPNT)
    (C A D : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ (F : Finset PrimitiveComplexCharacter) (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ),
        (∀ χ ∈ F, χ.modulus ≤ sparseConductorCutoff C L) →
        (∀ χ ∈ F, some χ ≠ exception) → ‖c₀‖ ≤ Real.exp (A * L) →
        (∀ χ ∈ F, ‖c χ‖ ≤ Real.exp (A * L)) →
        ‖c₀ * smoothMangoldtMean 1 1 (Real.exp (Real.exp L)) +
          ∑ χ ∈ F, c χ * smoothMangoldtMean χ.modulus χ.character (Real.exp (Real.exp L)) -
          c₀ * smoothPrincipalMain (Real.exp (Real.exp L))‖ ≤
          Real.exp (Real.exp L) * Real.exp (-D * L) := by
  filter_upwards [smooth_primitive_family_decay Z hD hR P hPNT (2 * C + 3) (D + A)
    (by linarith), eventual_sparseConductorCutoff C hC] with L hmean hcut
  obtain ⟨exception, hmean⟩ := hmean (sparseConductorCutoff C L) hcut.1 hcut.2.1 hcut.2.2
  refine ⟨exception, ?_⟩
  intro F c c₀ hF hFE hc₀ hc
  have hh := weighted_smooth_character_error F c c₀ (Real.exp (A * L))
    (Real.exp (Real.exp L)) hc₀ hc
  calc
    _ ≤ _ := hh
    _ ≤ Real.exp (A * L) * (Real.exp (Real.exp L) * Real.exp (-(D + A) * L)) :=
      mul_le_mul_of_nonneg_left (hmean F hF hFE) (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_left_comm (Real.exp (A * L)), ← Real.exp_add]
      congr 2
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseExpandedMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the analytic estimate to the actual sparse coefficients -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem sparseExpandedMangoldtMean_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (hPNT : PublishedSmoothPrincipalPNT)
    (C D : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
        (E : ∀ i, Finset (ZMod (p i))) (t : ℝ),
        (∀ i, 0 ∉ E i) → (∀ i b, -b ∈ E i ↔ b ∈ E i) →
        0 ≤ t → t ≤ 1 → (∀ i, (36 : ℝ) ≤ p i) →
        (∑ i, (p i : ℝ)⁻¹) ≤ L →
        (∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) →
        (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
        ‖sparseExpandedMangoldtMean p E t (sparseTruncationDegree C L) (Real.exp (Real.exp L)) -
          sparsePrimitiveCoefficient p E t (sparseTruncationDegree C L) none *
            smoothPrincipalMain (Real.exp (Real.exp L))‖ ≤
          Real.exp (Real.exp L) * Real.exp (-D * L) := by
  filter_upwards [weighted_sparse_character_decay Z hD hR P hPNT C 6 D hC] with L hL
  obtain ⟨exception, he⟩ := hL
  refine ⟨exception, ?_⟩
  intro n p hp hprod E t hE hsym ht ht1 hp36 hmass hlog havoid
  have hcoeff (e : Option PrimitiveComplexCharacter) :
      ‖sparsePrimitiveCoefficient p E t (sparseTruncationDegree C L) e‖ ≤ Real.exp (6 * L) := by
    exact (sparsePrimitiveCoefficient_norm_le p E hE hsym t ht ht1 hp36 _ e).trans
      (Real.exp_le_exp.mpr (by linarith))
  exact he (sparsePrimitiveSupport p E t (sparseTruncationDegree C L)).eraseNone
    (fun ρ => sparsePrimitiveCoefficient p E t (sparseTruncationDegree C L) (some ρ))
    (sparsePrimitiveCoefficient p E t (sparseTruncationDegree C L) none)
    (fun ρ hρ => sparsePrimitiveSupport_modulus_le p E C L t hlog ρ hρ)
    (sparsePrimitiveSupport_avoids p E t _ exception havoid) (hcoeff none)
    (fun ρ _ => hcoeff (some ρ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseKernelUnitFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unit-residue normalizing factor at the fixed kernel parameter -/

namespace Ostmann
open scoped Classical BigOperators

theorem sparseKernelUnitFactor_lower (p e ε : ℝ) (hp : 2 ≤ p)
    (he : 0 ≤ e) (heε : e ≤ ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - 4 * ε / p ≤ sparseKernelUnitFactor p e := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hn : -2 * ε ≤ ((17 / 20 : ℝ) ^ 2) * (e - e ^ 2) - (17 / 10) * e := by
    have he1 : e ≤ 1 := heε.trans hε1
    nlinarith
  have hfrac : -4 * ε / p ≤ -2 * ε / (p - 1) := by
    apply (div_le_div_iff₀ hp0 hp1).mpr
    nlinarith [mul_nonneg hε0 (sub_nonneg.mpr hp)]
  unfold sparseKernelUnitFactor
  calc
    1 - 4 * ε / p = 1 + (-4 * ε / p) := by ring
    _ ≤ 1 + (-2 * ε / (p - 1)) := add_le_add le_rfl hfrac
    _ ≤ _ := add_le_add le_rfl ((div_le_div_iff_of_pos_right hp1).mpr hn)

theorem sparseKernelUnitFactor_positive (p e ε : ℝ) (hp : 100 ≤ p)
    (he : 0 ≤ e) (heε : e ≤ ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 1000000) :
    0 < sparseKernelUnitFactor p e := by
  have hp0 : 0 < p := by linarith
  have hh := sparseKernelUnitFactor_lower p e ε (by linarith) he heε hε0 (by linarith)
  have heps : 4 * ε / p < 1 := (div_lt_one hp0).mpr (by linarith)
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_NonnegativeSparseWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real nonnegative weight represented by the truncated tensor -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem elementaryTruncation_conj {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ i, conj (b i) = b i) (K : ℕ) :
    conj (elementaryTruncation b K) = elementaryTruncation b K := by
  simp only [elementaryTruncation, map_sum, map_prod, hb]

theorem localSparseKernel_spectrum_real {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (x : ZMod p) :
    (localSparseKernel (largeTransformSpectrum (normalizedResidueTransform S)) x).im = 0 := by
  exact sparseAdditiveKernel_real _
    (largeTransformSpectrum_neg _ (normalizedResidueTransform_neg S)) (17 / 20) x

theorem sparseSubsetWeight_nonneg {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (x : ∀ i, ZMod (p i)) :
    0 ≤ sparseSubsetWeight p S K x := sq_nonneg _

theorem sparseSubsetWeight_complex {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (x : ∀ i, ZMod (p i)) :
    (sparseSubsetWeight p S K x : ℂ) =
      elementaryTruncation (fun i => localSparseKernel
        (largeTransformSpectrum (normalizedResidueTransform (S i))) (x i)) K ^ 2 := by
  let b := fun i => localSparseKernel (largeTransformSpectrum (normalizedResidueTransform (S i))) (x i)
  have hb (i) : conj (b i) = b i := by
    have hi : (b i).im = 0 := localSparseKernel_spectrum_real (S i) (x i)
    apply Complex.ext <;> simp [hi]
  have he := elementaryTruncation_conj b hb K
  have hh := Complex.mul_conj' (elementaryTruncation b K)
  rw [he, ← pow_two] at hh
  simpa only [sparseSubsetWeight, Complex.ofReal_pow, b] using hh.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseWeightUniformBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform pointwise bounds for the truncated sparse weight -/
namespace Ostmann
open scoped Classical BigOperators

 theorem elementaryTruncation_range {n : ℕ} (b : Fin n → ℂ) (K : ℕ) :
    elementaryTruncation b K = ∑ j ∈ Finset.range (K + 1), elementaryCoefficient b j := by
  let T := Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card ≤ K)
  have hmap : ∀ I ∈ T, I.card ∈ Finset.range (K + 1) := by
    intro I hI
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hI).2)
  have he := Finset.sum_fiberwise_of_maps_to hmap (fun I => ∏ i ∈ I, b i)
  change _ = elementaryTruncation b K at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro j hj
  unfold elementaryCoefficient
  apply Finset.sum_congr
  · ext I
    simp only [T, Finset.mem_filter]
    have hjK := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    constructor
    · rintro ⟨⟨hp, _⟩, he⟩
      exact ⟨hp, he⟩
    · rintro ⟨hp, rfl⟩
      exact ⟨⟨hp, hjK⟩, rfl⟩
  · intro I hI
    rfl

 theorem elementaryCoefficient_norm_le_choose {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ i, ‖b i‖ ≤ 1) (j : ℕ) :
    ‖elementaryCoefficient b j‖ ≤ n.choose j := by
  unfold elementaryCoefficient
  calc
    _ ≤ ∑ I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card = j),
      ‖∏ i ∈ I, b i‖ := norm_sum_le _ _
    _ ≤ ∑ _I ∈ Finset.univ.powerset.filter (fun I : Finset (Fin n) => I.card = j), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hb i)
    _ = _ := by rw [← Finset.powersetCard_eq_filter]; simp

 theorem elementaryTruncation_norm_le {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ i, ‖b i‖ ≤ 1) (K : ℕ) :
    ‖elementaryTruncation b K‖ ≤ (K + 1 : ℝ) * (n + 1 : ℝ) ^ K := by
  rw [elementaryTruncation_range]
  calc
    _ ≤ ∑ j ∈ Finset.range (K + 1), ‖elementaryCoefficient b j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (K + 1), (n + 1 : ℝ) ^ K := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ (n.choose j : ℝ) := elementaryCoefficient_norm_le_choose b hb j
        _ ≤ (n : ℝ) ^ j := by exact_mod_cast Nat.choose_le_pow n j
        _ ≤ (n + 1 : ℝ) ^ j := by gcongr; linarith
        _ ≤ (n + 1 : ℝ) ^ K :=
          pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = _ := by simp

 theorem localSparseKernel_norm_le_one {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (x : ZMod p) : ‖localSparseKernel E x‖ ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hc : (E.card : ℝ) ≤ p := by
    have hh := Finset.card_le_card (Finset.subset_univ E)
    simpa only [Finset.card_univ, ZMod.card] using (Nat.cast_le (α := ℝ)).mpr hh
  apply (sparseAdditiveKernel_norm_le E (17 / 20) (by norm_num) x).trans
  have he : (E.card : ℝ) / p ≤ 1 := (div_le_one hp).mpr hc
  calc
    _ = (17 / 20 : ℝ) * (E.card / p) := by ring
    _ ≤ (17 / 20 : ℝ) * 1 := mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ 1 := by norm_num

 theorem sparseSubsetWeight_uniform_bound {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (x : ∀ i, ZMod (p i)) :
    sparseSubsetWeight p S K x ≤ ((K + 1 : ℝ) * (n + 1 : ℝ) ^ K) ^ 2 := by
  exact pow_le_pow_left₀ (norm_nonneg _)
    (elementaryTruncation_norm_le _ (fun i => localSparseKernel_norm_le_one _ _) K) 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseWeightGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The truncated weight grows more slowly than every fixed power of X -/
namespace Ostmann
open Filter

theorem sparse_weight_uniform_exponential (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (n : ℕ) (hn : (n : ℝ) ≤ Real.exp (Real.exp ((9 / 10 : ℝ) * L))) :
    (((sparseTruncationDegree C L : ℕ) + 1 : ℝ) *
      (n + 1 : ℝ) ^ sparseTruncationDegree C L) ^ 2 ≤
      Real.exp ((6 * C + 8) * L * Real.exp ((9 / 10 : ℝ) * L)) := by
  let K := sparseTruncationDegree C L
  let E := Real.exp ((9 / 10 : ℝ) * L)
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have hK : (K : ℝ) ≤ (C + 1) * L := by
    have hh := (Nat.ceil_lt_add_one (mul_nonneg hC (show 0 ≤ L by linarith))).le
    change (K : ℝ) ≤ C * L + 1 at hh
    nlinarith
  have hKexp : (K + 1 : ℝ) ≤ Real.exp ((C + 2) * L) := by
    apply le_trans _ (Real.add_one_le_exp ((C + 2) * L))
    nlinarith
  have hnexp : (n + 1 : ℝ) ≤ Real.exp (2 * E) := by
    have he := Real.add_one_le_exp E
    have hh : (n + 1 : ℝ) ≤ 2 * Real.exp E := by
      have hh' : 1 ≤ Real.exp E := Real.one_le_exp (by linarith)
      dsimp [E] at hh'
      linarith
    apply hh.trans
    calc
      _ ≤ Real.exp E * Real.exp E := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : (n + 1 : ℝ) ^ K ≤ Real.exp ((K : ℝ) * (2 * E)) := by
    calc
      _ ≤ (Real.exp (2 * E)) ^ K := pow_le_pow_left₀ (by positivity) hnexp K
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hh : ((K + 1 : ℝ) * (n + 1 : ℝ) ^ K) ^ 2 ≤
      (Real.exp ((C + 2) * L) * Real.exp ((K : ℝ) * (2 * E))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul hKexp hp (by positivity) (Real.exp_nonneg _)) 2
  apply hh.trans
  rw [← Real.exp_add, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hK (show 0 ≤ E by linarith)
  have hCmul := mul_le_mul_of_nonneg_left hE (show 0 ≤ (C + 2) * L by positivity)
  dsimp [K, E] at *
  norm_num
  nlinarith

 theorem eventual_sparse_weight_subpower (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ,
      (n : ℝ) ≤ Real.exp (Real.exp ((9 / 10 : ℝ) * L)) →
      (((sparseTruncationDegree C L : ℕ) + 1 : ℝ) *
        (n + 1 : ℝ) ^ sparseTruncationDegree C L) ^ 2 ≤
        Real.exp (δ * Real.exp L) := by
  have hs := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul_left (6 * C + 8)).bound hδ
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with L hsmall hL n hn
  apply (sparse_weight_uniform_exponential C L hC hL n hn).trans
  apply Real.exp_le_exp.mpr
  have hsmall' : (6 * C + 8) * L ≤ δ * Real.exp ((1 / 10 : ℝ) * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (6 * C + 8) * L),
      abs_of_pos (Real.exp_pos _)] using hsmall
  have hh := mul_le_mul_of_nonneg_right hsmall' (Real.exp_nonneg ((9 / 10 : ℝ) * L))
  have he : Real.exp ((1 / 10 : ℝ) * L) * Real.exp ((9 / 10 : ℝ) * L) = Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [mul_assoc δ, he] at hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePrimeFamilyCard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cardinality bound for the distinct selected primes -/
namespace Ostmann
open scoped Classical BigOperators

 theorem prime_family_injective {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hh := hc hij
  change (p i).Coprime (p j) at hh
  rw [he, Nat.coprime_self] at hh
  exact (Fact.out : (p j).Prime).ne_one hh

 theorem sparse_prime_family_card {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (L : ℝ) (hp : ∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) :
    (n : ℝ) ≤ Real.exp (Real.exp ((9 / 10 : ℝ) * L)) := by
  let R := Real.exp (Real.exp ((9 / 10 : ℝ) * L))
  have hsub : Finset.univ.image p ⊆ Finset.Icc 1 ⌊R⌋₊ := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_Icc.mpr ⟨(Fact.out : (p i).Prime).one_le, Nat.le_floor ?_⟩
    exact (Real.log_le_iff_le_exp (by exact_mod_cast (Fact.out : (p i).Prime).pos)).mp (hp i)
  have hn : n ≤ ⌊R⌋₊ := by
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_image_of_injective _ (prime_family_injective p hc),
      Finset.card_univ, Fintype.card_fin, Nat.card_Icc, Nat.sub_zero, Nat.add_sub_cancel] using hh
  exact (Nat.cast_le.mpr hn).trans (Nat.floor_le (Real.exp_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePrimeIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The primitive expansion agrees with the original weight on the supported primes -/
namespace Ostmann
open scoped Classical BigOperators

 theorem supported_prime_coprime {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (X : ℝ) (hX : 0 < X) (hp : ∀ i, (p i : ℝ) ≤ X / 2)
    (q : ℕ) (hq : q.Prime) (ht : primeMeanTest (q / X) ≠ 0) :
    q.Coprime (∏ i, p i) := by
  have hmem : (q : ℝ) / X ∈ Set.Icc (5 / 8 : ℝ) (7 / 8) := by
    by_contra h
    exact ht (primeMeanTest_zero_outside _ h)
  have hqX := (le_div_iff₀ hX).mp hmem.1
  apply Nat.coprime_prod_right_iff.mpr
  intro i _
  apply (Nat.coprime_primes hq (Fact.out : (p i).Prime)).mpr
  intro he
  have hh := hp i
  rw [← he] at hh
  linarith

 theorem sparsePrimeSum_identity {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (X : ℝ) (hX : 0 < X) (hp : ∀ i, (p i : ℝ) ≤ X / 2) :
    let E := fun i => largeTransformSpectrum (normalizedResidueTransform (S i))
    smoothPrimeSum (primitiveCharacterPolynomial
      (sparsePrimitiveSupport p E (17 / 20) K).eraseNone
      (fun ρ => sparsePrimitiveCoefficient p E (17 / 20) K (some ρ))
      (sparsePrimitiveCoefficient p E (17 / 20) K none)) X =
    ((∑ q ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      Real.log q * sparseSubsetWeight p S K (fun i => (q : ZMod (p i))) *
        primeMeanTest (q / X) : ℝ) : ℂ) := by
  intro E
  simp only [smoothPrimeSum, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases ht : primeMeanTest (q / X) = 0
  · simp only [ht, Complex.ofReal_zero, mul_zero]
  · have hh := sparseWeight_integer_expansion p hc E (17 / 20) K q
      (supported_prime_coprime p X hX hp q (Finset.mem_filter.mp hq).2 ht)
    have hw := sparseSubsetWeight_complex p S K (fun i => (q : ZMod (p i)))
    change (sparseSubsetWeight p S K (fun i => (q : ZMod (p i))) : ℂ) =
      elementaryTruncation (fun i => sparseAdditiveKernel (E i) (17 / 20) (q : ZMod (p i))) K ^ 2 at hw
    rw [hw, hh]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseUnitMassBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lower and upper bounds for the full unit normalizer -/

namespace Ostmann
open scoped Classical BigOperators

theorem exp_neg_two_le_one_sub (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hp : 0 < 1 - x := by linarith
  have hi : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hl := Real.one_sub_inv_le_log_of_pos hp
  rw [← Real.exp_log hp]
  exact Real.exp_le_exp.mpr (by linarith)

theorem sparseKernelUnitFactor_upper (p e : ℝ) (hp : 1 < p) (he : 0 ≤ e) :
    sparseKernelUnitFactor p e ≤ 1 := by
  unfold sparseKernelUnitFactor
  have hn : (17 / 20 : ℝ) ^ 2 * (e - e ^ 2) - (17 / 10) * e ≤ 0 := by
    nlinarith [sq_nonneg e]
  have hh := div_nonpos_of_nonpos_of_nonneg hn (show 0 ≤ p - 1 by linarith)
  linarith

theorem sparseKernelUnitFactor_exp_lower (p e ε : ℝ) (hp : 100 ≤ p)
    (he : 0 ≤ e) (heε : e ≤ ε) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000) :
    Real.exp (-8 * ε / p) ≤ sparseKernelUnitFactor p e := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ 4 * ε / p := by positivity
  have hx1 : 4 * ε / p ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hh := exp_neg_two_le_one_sub (4 * ε / p) hx0 hx1
  have hl := sparseKernelUnitFactor_lower p e ε (by linarith) he heε hε (by linarith)
  apply le_trans _ hl
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

theorem sparse_unit_mass_range {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (E : ∀ i, Finset (ZMod (p i))) (hp : ∀ i, (100 : ℝ) ≤ p i)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hc : ∀ i, ((E i).card : ℝ) ≤ ε * p i) :
    let U := ∏ i, sparseKernelUnitFactor (p i) (((E i).card : ℝ) / p i)
    Real.exp (-8 * ε * ∑ i, (p i : ℝ)⁻¹) ≤ U ∧ U ≤ 1 := by
  intro U
  have hratio (i : Fin n) : ((E i).card : ℝ) / p i ≤ ε :=
    (div_le_iff₀ (show (0 : ℝ) < p i by linarith [hp i])).mpr (hc i)
  constructor
  · have hh := Finset.prod_le_prod (s := Finset.univ)
      (fun (i : Fin n) _ => (Real.exp_pos (-8 * ε / p i)).le)
      (fun (i : Fin n) _ => sparseKernelUnitFactor_exp_lower (p i) _ ε (hp i)
        (by positivity) (hratio i) hε hεsmall)
    rw [← Real.exp_sum] at hh
    simpa only [U, div_eq_mul_inv, ← Finset.mul_sum] using hh
  · apply Finset.prod_le_one
    · intro i _
      exact (sparseKernelUnitFactor_positive (p i) _ ε (hp i) (by positivity)
        (hratio i) hε hεsmall).le
    · intro i _
      exact sparseKernelUnitFactor_upper _ _ (by linarith [hp i]) (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseWeightUnitMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact real unit mean of the nonnegative sparse weight -/

namespace Ostmann
open scoped Classical BigOperators

theorem tensorUnitMean_ofReal {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (f : (∀ i, ZMod (p i)) → ℝ) :
    tensorUnitMean p (fun x => (f x : ℂ)) = (tensorRealUnitMean p f : ℂ) := by
  unfold tensorUnitMean tensorRealUnitMean
  push_cast
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimePowerDecayRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Higher-prime-power errors at the sparse conductor scale -/
namespace Ostmann
open Filter

theorem eventual_prime_power_error (a A D : ℝ) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      Real.log Q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      (Real.exp (A * L) * (1 + (Q : ℝ) ^ 2)) *
        (2 * Real.sqrt (Real.exp (Real.exp L)) * Real.log (Real.exp (Real.exp L))) ≤
      Real.exp (Real.exp L) * Real.exp (-D * L) := by
  filter_upwards [eventual_conductor_exponential_decay a 2 4 (D + A + 1) ha (by norm_num)]
    with L hL Q hQ hlog
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hq2 : 1 + (Q : ℝ) ^ 2 ≤ 2 * (Q : ℝ) ^ 2 := by nlinarith
  have hd := hL (Real.log Q) (Real.log_nonneg hQ1) hlog
  have hpow : (Q : ℝ) ^ 2 = Real.exp (2 * Real.log Q) := by
    rw [show (2 : ℝ) * Real.log Q = Real.log Q + Real.log Q by ring,
      Real.exp_add, Real.exp_log hQ0, pow_two]
  calc
    _ ≤ (Real.exp (A * L) * (2 * (Q : ℝ) ^ 2)) *
        (2 * Real.sqrt (Real.exp (Real.exp L)) * Real.log (Real.exp (Real.exp L))) := by
      gcongr
      rw [Real.log_exp]
      positivity
    _ = (Real.exp (Real.exp L) * Real.exp ((A + 1) * L)) *
        (4 * Real.exp (2 * Real.log Q - Real.exp L / 2)) := by
      rw [hpow, Real.sqrt_eq_rpow, ← Real.exp_mul, Real.log_exp]
      have he : Real.exp (A * L) * Real.exp (2 * Real.log Q) *
          Real.exp (Real.exp L * (1 / 2)) * Real.exp L =
          Real.exp (Real.exp L) * Real.exp ((A + 1) * L) *
            Real.exp (2 * Real.log Q - Real.exp L / 2) := by
        simp only [← Real.exp_add]
        congr 1
        ring
      calc
        _ = 4 * (Real.exp (A * L) * Real.exp (2 * Real.log Q) *
            Real.exp (Real.exp L * (1 / 2)) * Real.exp L) := by ring
        _ = _ := by rw [he]; ring
    _ ≤ (Real.exp (Real.exp L) * Real.exp ((A + 1) * L)) *
        Real.exp (-(D + A + 1) * L) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem eventual_sparse_prime_below_half :
    ∀ᶠ L : ℝ in atTop, ∀ p : ℕ, 1 ≤ p →
      Real.log p ≤ Real.exp ((9 / 10 : ℝ) * L) →
      (p : ℝ) ≤ Real.exp (Real.exp L) / 2 := by
  filter_upwards [eventual_conductor_exponential_decay 1 1 2 0 (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hdec hL p hp hlog
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hd := hdec (Real.log p) (Real.log_nonneg hp1)
    (hlog.trans (by nlinarith [Real.exp_pos ((9 / 10 : ℝ) * L)]))
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul] at hd
  have hh := mul_le_mul_of_nonneg_right hd (Real.exp_nonneg (Real.exp L / 2))
  have hid : (2 * Real.exp (Real.log p - Real.exp L / 2)) * Real.exp (Real.exp L / 2) =
      2 * p := by
    rw [mul_assoc, ← Real.exp_add, sub_add_cancel, Real.exp_log hp0]
  rw [hid, one_mul] at hh
  have he : Real.exp (Real.exp L / 2) ≤ Real.exp (Real.exp L) :=
    Real.exp_le_exp.mpr (by linarith [Real.exp_pos L])
  linarith

theorem eventual_sparse_prime_error_margin (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, 2 * Real.exp (-10 * L) ≤ c / 4 * Real.exp (-L) := by
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually_le_const
    (show 0 < c / 8 by positivity), eventually_ge_atTop (0 : ℝ)] with L hh hL
  have h9 : Real.exp (-9 * L) ≤ c / 8 :=
    (Real.exp_le_exp.mpr (by linarith)).trans hh
  calc
    _ = (2 * Real.exp (-9 * L)) * Real.exp (-L) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (c / 4) * Real.exp (-L) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SparsePrincipalMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The principal coefficient is the exact unit-residue mean -/
namespace Ostmann
open scoped Classical BigOperators

theorem sparsePrimitiveCoefficient_principal {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) :
    sparsePrimitiveCoefficient p E t K none =
      sparseTruncatedMellinCoefficient p E t K (fun _ => 1) := by
  have hlabel : sparsePrimitiveLabel p (fun _ => 1) = none := by
    simp [sparsePrimitiveLabel, sparseProductCharacter, primitiveCharacterReduction]
  rw [← hlabel]
  exact injectiveCoefficient_apply _ (sparsePrimitiveLabel_injective p hc) _ _

theorem productCharacter_unit_sum {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) :
    (∑ x : (∀ i, (ZMod (p i))ˣ), ∏ i, χ i (x i)) =
      if χ = (fun _ => 1) then ∏ i, (Fintype.card (ZMod (p i))ˣ : ℂ) else 0 := by
  rw [← Fintype.prod_sum (fun i (x : (ZMod (p i))ˣ) => χ i x)]
  simp_rw [sum_mulChar_units_eq_ite]
  by_cases hχ : χ = (fun _ => 1)
  · subst χ
    simp
  · rw [ite_eq_right hχ]
    obtain ⟨i, hi⟩ : ∃ i, χ i ≠ 1 := by
      by_contra! hh
      exact hχ (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

noncomputable local instance instFintypeMulCharZModComplexOfFactPrime_solutions_6_r209b90_1 {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _
theorem sparsePrimitiveCoefficient_unit_mean {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) :
    sparsePrimitiveCoefficient p E t K none =
      (∏ i, (Fintype.card (ZMod (p i))ˣ : ℂ)⁻¹) *
        ∑ x : (∀ i, (ZMod (p i))ˣ),
          elementaryTruncation (fun i => sparseAdditiveKernel (E i) t (x i)) K ^ 2 := by
  have hsum : (∑ x : (∀ i, (ZMod (p i))ˣ),
      elementaryTruncation (fun i => sparseAdditiveKernel (E i) t (x i)) K ^ 2) =
      sparseTruncatedMellinCoefficient p E t K (fun _ => 1) *
        ∏ i, (Fintype.card (ZMod (p i))ˣ : ℂ) := by
    simp_rw [sparseWeight_mellin_expansion]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, productCharacter_unit_sum]
    simp
  rw [hsum, sparsePrimitiveCoefficient_principal p hc, Finset.prod_inv_distrib]
  have hd : (∏ i, (Fintype.card (ZMod (p i))ˣ : ℂ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem sparsePrimitiveCoefficient_tensor_mean {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) :
    sparsePrimitiveCoefficient p E t K none =
      tensorUnitMean p (fun x => elementaryTruncation
        (fun i => sparseAdditiveKernel (E i) t (x i)) K ^ 2) := by
  rw [sparsePrimitiveCoefficient_unit_mean p hc]
  unfold tensorUnitMean
  have hcard (i : Fin n) : (Fintype.card (ZMod (p i))ˣ : ℂ) = (p i : ℂ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : (p i).Prime).one_lt.le, Nat.cast_one]
  simp only [hcard]
  congr 1
  let e := Equiv.piCongrRight (fun i : Fin n => unitNonzeroResidueEquiv (p i))
  have he := e.sum_comp (fun x => elementaryTruncation
    (fun i => sparseAdditiveKernel (E i) t ((x i : NonzeroResidue (p i)) : ZMod (p i))) K ^ 2)
  exact he

theorem sparsePrimitiveCoefficient_real_mean {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) :
    sparsePrimitiveCoefficient p (fun i => largeTransformSpectrum (normalizedResidueTransform (S i)))
      (17 / 20) K none = (tensorRealUnitMean p (sparseSubsetWeight p S K) : ℂ) := by
  rw [sparsePrimitiveCoefficient_tensor_mean p hc, ← tensorUnitMean_ofReal]
  apply congrArg (tensorUnitMean p)
  funext x
  exact (sparseSubsetWeight_complex p S K x).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePrimeMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-weighted mean of the actual sparse subset weight -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

 theorem sparseWeightedPrimeSum_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (hPNT : PublishedSmoothPrincipalPNT)
    (C D : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
        (S : ∀ i, Finset (ZMod (p i))),
        Pairwise (fun i j => (p i).Coprime (p j)) →
        (∀ i, (36 : ℝ) ≤ p i) → (∑ i, (p i : ℝ)⁻¹) ≤ L →
        (∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) →
        (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp L) / 2) →
        (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
        |sparseWeightedPrimeSum p S (sparseTruncationDegree C L) (Real.exp (Real.exp L)) -
          tensorRealUnitMean p (sparseSubsetWeight p S (sparseTruncationDegree C L)) *
            (Real.exp (Real.exp L) * ∫ t : ℝ, primeMeanTest t)| ≤
          2 * Real.exp (Real.exp L) * Real.exp (-D * L) := by
  filter_upwards [sparseExpandedMangoldtMean_decay Z hD hR P hPNT C D hC,
    eventual_prime_power_error (2 * C + 3) 6 D (by linarith),
    eventually_ge_atTop (1 : ℝ)] with L hmean hpp hL
  obtain ⟨exception, he⟩ := hmean
  refine ⟨exception, ?_⟩
  intro n p hp hprod S hc hp36 hmass hlog hbound havoid
  let E := fun i => largeTransformSpectrum (normalizedResidueTransform (S i))
  let K := sparseTruncationDegree C L
  let X := Real.exp (Real.exp L)
  let F := (sparsePrimitiveSupport p E (17 / 20) K).eraseNone
  let c := fun ρ => sparsePrimitiveCoefficient p E (17 / 20) K (some ρ)
  let c₀ := sparsePrimitiveCoefficient p E (17 / 20) K none
  have hE (i) : 0 ∉ E i :=
    largeTransformSpectrum_zero_not_mem _ (normalizedResidueTransform_zero (S i))
  have hsym (i) : ∀ b, -b ∈ E i ↔ b ∈ E i :=
    largeTransformSpectrum_neg _ (normalizedResidueTransform_neg (S i))
  have hcoeff (e : Option PrimitiveComplexCharacter) :
      ‖sparsePrimitiveCoefficient p E (17 / 20) K e‖ ≤ Real.exp (6 * L) := by
    exact (sparsePrimitiveCoefficient_norm_le p E hE hsym (17 / 20) (by norm_num)
      (by norm_num) hp36 K e).trans (Real.exp_le_exp.mpr (by linarith))
  have hQ (ρ) (hρ : ρ ∈ F) : ρ.modulus ≤ sparseConductorCutoff C L :=
    sparsePrimitiveSupport_modulus_le p E C L (17 / 20) hlog ρ hρ
  have hX : 1 ≤ X := Real.one_le_exp (Real.exp_nonneg L)
  have hA := he n p E (17 / 20) hE hsym (by norm_num) (by norm_num) hp36 hmass hlog havoid
  have hB := character_prime_power_error_of_conductor F c c₀ X (Real.exp (6 * L)) hX
    (Real.exp_nonneg _) (hcoeff none) (fun ρ _ => hcoeff (some ρ))
    (sparseConductorCutoff C L) hQ
  have hrate := hpp (sparseConductorCutoff C L) (sparseConductorCutoff_pos C L)
    (sparseConductorCutoff_log_upper C L hC.le hL)
  have hid := sparsePrimeSum_identity p hc S K X (Real.exp_pos _) hbound
  change smoothPrimeSum (primitiveCharacterPolynomial F c c₀) X =
    (sparseWeightedPrimeSum p S K X : ℂ) at hid
  have hcmean := sparsePrimitiveCoefficient_real_mean p hc S K
  have hmain : c₀ * smoothPrincipalMain X =
      ((tensorRealUnitMean p (sparseSubsetWeight p S K) *
        (X * ∫ t : ℝ, primeMeanTest t) : ℝ) : ℂ) := by
    rw [show c₀ = _ from hcmean]
    simp only [smoothPrincipalMain, Complex.ofReal_mul]
  have htri := (norm_sub_le_norm_sub_add_norm_sub (smoothPrimeSum (primitiveCharacterPolynomial F c c₀) X)
    (sparseExpandedMangoldtMean p E (17 / 20) K X) (c₀ * smoothPrincipalMain X)).trans
      (add_le_add (by simpa only [norm_sub_rev, sparseExpandedMangoldtMean, F, c, c₀] using hB.trans hrate) hA)
  rw [hid, hmain, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htri
  convert htri using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparsePrimeLowerBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive prime mean for the actual contracting weight -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

 theorem sparseWeightedPrimeSum_lower (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (hPNT : PublishedSmoothPrincipalPNT)
    (C : ℝ) (hC : 1000 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
        (S : ∀ i, Finset (ZMod (p i))),
        Pairwise (fun i j => (p i).Coprime (p j)) →
        (∀ i, (S i).Nonempty) → (∀ i, (S i).card < p i) →
        (∀ i, (100 : ℝ) ≤ p i) →
        (∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i)) →
        (∀ i, residueDensity (S i) ≤ 2 / 3) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 1000000 →
        (∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2) →
        (∑ i, (p i : ℝ)⁻¹) ≤ L →
        (∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) →
        (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
        let U := ∏ i, sparseKernelUnitFactor (p i)
          (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
        0 < U ∧ Real.exp (-L) ≤ U ∧ ((∫ t : ℝ, primeMeanTest t) / 4) * U * Real.exp (Real.exp L) ≤
          sparseWeightedPrimeSum p S (sparseTruncationDegree C L) (Real.exp (Real.exp L)) := by
  filter_upwards [sparseWeightedPrimeSum_decay Z hD hR P hPNT C 10 (by linarith),
    eventual_sparse_prime_error_margin (∫ t : ℝ, primeMeanTest t) primeMeanTest_integral_pos,
    eventual_sparse_prime_below_half, eventually_ge_atTop (1 : ℝ)] with L hmean hmargin hhalf hL
  obtain ⟨exception, he⟩ := hmean
  refine ⟨exception, ?_⟩
  intro n p hp hprod S hc hS hSp hp100 hlo hhi ε hε hεsmall hL1 hH hlog havoid U
  let K := sparseTruncationDegree C L
  let H := ∑ i, (p i : ℝ)⁻¹
  let E := fun i => largeTransformSpectrum (normalizedResidueTransform (S i))
  let X := Real.exp (Real.exp L)
  let I := ∫ t : ℝ, primeMeanTest t
  have hK : 1000 * L ≤ K :=
    (mul_le_mul_of_nonneg_right hC (by linarith)).trans (Nat.le_ceil _)
  obtain ⟨hU, hunit, _⟩ := sparse_finite_contraction p S hS hSp hp100 hlo hhi ε hε hεsmall
    hL1 L hL hH K hK
  have hspec (i) := normalizedResidueTransform_sparse (S i) (hS i) (hSp i)
    ε (ε ^ 2) (by nlinarith) le_rfl (hL1 i)
  have hlow := (sparse_unit_mass_range p E hp100 ε hε hεsmall
    (fun i => (hspec i).2.2.1)).1
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun _ _ => by positivity)
  have hucoarse : Real.exp (-L) ≤ U := by
    apply le_trans _ hlow
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (show 8 * ε ≤ 1 by linarith) hH0
    change _ ≤ -8 * ε * H
    dsimp [H] at hh ⊢
    linarith
  refine ⟨hU, hucoarse, ?_⟩
  have hm := he n p S hc (fun i => by linarith [hp100 i]) hH hlog
    (fun i => hhalf (p i) (Fact.out : (p i).Prime).one_le (hlog i)) havoid
  change |sparseWeightedPrimeSum p S K X - tensorRealUnitMean p (sparseSubsetWeight p S K) *
    (X * I)| ≤ 2 * X * Real.exp (-10 * L) at hm
  have herr : 2 * X * Real.exp (-10 * L) ≤ (I / 4) * U * X := by
    calc
      _ = (2 * Real.exp (-10 * L)) * X := by ring
      _ ≤ ((I / 4) * Real.exp (-L)) * X :=
        mul_le_mul_of_nonneg_right hmargin (Real.exp_nonneg _)
      _ ≤ (I / 4) * U * X := by
        gcongr
        exact div_nonneg primeMeanTest_integral_pos.le (by norm_num)
  have hbase := mul_le_mul_of_nonneg_right hunit
    (mul_nonneg (Real.exp_nonneg (Real.exp L)) primeMeanTest_integral_pos.le)
  have helo := (abs_le.mp hm).1
  change U / 2 * (X * I) ≤ _ at hbase
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeCoverageWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Converting full prime coverage into a nonnegative pair-weight bound -/
namespace Ostmann
open scoped Classical BigOperators

 theorem covered_weight_sum_le (P A B : Finset ℕ) (W : ℕ → ℝ)
    (hW : ∀ n, 0 ≤ W n)
    (hcover : ∀ q ∈ P, ∃ a ∈ A, ∃ b ∈ B, a + b = q) :
    (∑ q ∈ P, W q) ≤ ∑ a ∈ A, ∑ b ∈ B, W (a + b) := by
  let f : ℕ × ℕ → ℕ := fun ab => ab.1 + ab.2
  have hsub : P ⊆ (A ×ˢ B).image f := by
    intro q hq
    obtain ⟨a, ha, b, hb, h⟩ := hcover q hq
    exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, h⟩
  calc
    _ ≤ ∑ q ∈ (A ×ˢ B).image f, W q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hW q)
    _ ≤ ∑ ab ∈ A ×ˢ B, W (f ab) :=
      Finset.sum_image_le_of_nonneg (fun q _ => hW q)
    _ = _ := Finset.sum_product A B (fun ab => W (f ab))

 theorem smooth_covered_weight_le (P A B : Finset ℕ) (W : ℕ → ℝ) (X : ℝ)
    (hX : 1 ≤ X) (hW : ∀ n, 0 ≤ W n)
    (hP : ∀ q ∈ P, 0 < q ∧ (q : ℝ) ≤ X)
    (hcover : ∀ q ∈ P, ∃ a ∈ A, ∃ b ∈ B, a + b = q) :
    (∑ q ∈ P, Real.log q * W q * primeMeanTest (q / X)) ≤
      Real.log X * ∑ a ∈ A, ∑ b ∈ B, W (a + b) := by
  calc
    _ ≤ ∑ q ∈ P, Real.log X * W q := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (hP q hq).1
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (hP q hq).1
      calc
        _ ≤ Real.log q * W q * 1 :=
          mul_le_mul_of_nonneg_left (primeMeanTest_le_one _)
            (mul_nonneg (Real.log_nonneg hq1) (hW q))
        _ ≤ Real.log X * W q := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (Real.log_le_log hq0 (hP q hq).2) (hW q)
    _ = Real.log X * ∑ q ∈ P, W q := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (covered_weight_sum_le P A B W hW hcover)
      (Real.log_nonneg hX)

 theorem EventuallyPrimeSumset.smooth_coverage {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N : ℕ, ∀ X : ℝ, 1 ≤ X → 2 * N ≤ X → ∀ W : ℕ → ℝ, (∀ n, 0 ≤ W n) →
      (∑ q ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
        Real.log q * W q * primeMeanTest (q / X)) ≤
      Real.log X * ∑ a ∈ summandPrefix A ⌊X⌋₊,
        ∑ b ∈ summandPrefix B ⌊X⌋₊, W (a + b) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro X hX hNX W hW
  let P := ((Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime).filter
    (fun q : ℕ => primeMeanTest ((q : ℝ) / X) ≠ 0)
  have hsum : (∑ q ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      Real.log q * W q * primeMeanTest (q / X)) =
      ∑ q ∈ P, Real.log q * W q * primeMeanTest (q / X) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hnot
    have ht : primeMeanTest (q / X) = 0 := by simpa only [P, Finset.mem_filter, hq, true_and, not_not] using hnot
    rw [ht, mul_zero]
  rw [hsum]
  apply smooth_covered_weight_le P _ _ W X hX hW
  · intro q hq
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    exact ⟨(Finset.mem_Ioc.mp hh).1,
      (Nat.le_floor_iff (by linarith)).mp (Finset.mem_Ioc.mp hh).2⟩
  · intro q hq
    obtain ⟨hqP, htest⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqr, hprime⟩ := Finset.mem_filter.mp hqP
    have hqX : q ≤ ⌊X⌋₊ := (Finset.mem_Ioc.mp hqr).2
    have hmem : (q : ℝ) / X ∈ Set.Icc (5 / 8 : ℝ) (7 / 8) := by
      by_contra hout
      exact htest (primeMeanTest_zero_outside _ hout)
    have hqN : N ≤ q := by
      have hh := (le_div_iff₀ (show 0 < X by linarith)).mp hmem.1
      have : (N : ℝ) ≤ q := by linarith
      exact_mod_cast this
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sumset.mp ((hN q hqN).mpr hprime)
    exact ⟨a, (mem_summandPrefix A _ _).mpr ⟨ha, by omega⟩,
      b, (mem_summandPrefix B _ _).mpr ⟨hb, by omega⟩, hab⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailPairDeletion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cost of removing small endpoints from a nonnegative pair sum -/
namespace Ostmann
open scoped Classical BigOperators

 theorem pair_sum_filter_error (A B : Finset ℕ) (lo : ℕ) (W : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hW : ∀ a ∈ A, ∀ b ∈ B, W (a + b) ≤ M) :
    (∑ a ∈ A, ∑ b ∈ B, W (a + b)) ≤
      (∑ a ∈ A.filter (fun a => lo < a), ∑ b ∈ B.filter (fun b => lo < b), W (a + b)) +
      M * (((A.filter (fun a => a ≤ lo)).card : ℝ) * B.card +
        (A.card : ℝ) * (B.filter (fun b => b ≤ lo)).card) := by
  have hp (a) (ha : a ∈ A) (b) (hb : b ∈ B) :
      W (a + b) ≤ (if lo < a then if lo < b then W (a + b) else 0 else 0) +
        (if a ≤ lo then M else 0) + (if b ≤ lo then M else 0) := by
    by_cases hla : lo < a <;> by_cases hlb : lo < b
    · simp only [hla, hlb, ite_true, if_true, Nat.not_le.mpr hla, Nat.not_le.mpr hlb, ite_false, if_false, add_zero]
      exact le_rfl
    · simp only [hla, hlb, ite_true, if_true, ite_false, if_false, Nat.not_le.mpr hla,
        Nat.le_of_not_lt hlb, zero_add]
      exact hW a ha b hb
    · simp only [hla, hlb, ite_true, if_true, ite_false, if_false, Nat.le_of_not_lt hla,
        Nat.not_le.mpr hlb, zero_add, add_zero]
      exact hW a ha b hb
    · simp only [hla, hlb, ite_true, if_true, ite_false, if_false, Nat.le_of_not_lt hla,
        Nat.le_of_not_lt hlb, zero_add]
      exact (hW a ha b hb).trans (by linarith)
  have hh := Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hp a ha b hb))
  have hg : (∑ a ∈ A, ∑ b ∈ B,
      if lo < a then if lo < b then W (a + b) else 0 else 0) =
      ∑ a ∈ A.filter (fun a => lo < a), ∑ b ∈ B.filter (fun b => lo < b), W (a + b) := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, ← Finset.sum_filter]
  have hA : (∑ a ∈ A, ∑ _b ∈ B, if a ≤ lo then M else 0) =
      ((A.filter (fun a => a ≤ lo)).card : ℝ) * B.card * M := by
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [← Finset.sum_filter]
    simp
    ring
  have hB : (∑ _a ∈ A, ∑ b ∈ B, if b ≤ lo then M else 0) =
      (A.card : ℝ) * (B.filter (fun b => b ≤ lo)).card * M := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  simp only [Finset.sum_add_distrib] at hh
  rw [hg, hA, hB] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

 theorem prefix_pair_sum_le_tail (A B : Set ℕ) (lo X : ℕ) (hlo : lo ≤ X)
    (W : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hW : ∀ n, W n ≤ M) :
    (∑ a ∈ summandPrefix A X, ∑ b ∈ summandPrefix B X, W (a + b)) ≤
      (∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X, W (a + b)) +
      M * (((summandPrefix A lo).card : ℝ) * (summandPrefix B X).card +
        ((summandPrefix A X).card : ℝ) * (summandPrefix B lo).card) := by
  have ht (T : Set ℕ) : (summandPrefix T X).filter (fun a => lo < a) = summandTail T lo X := by
    ext a
    simp only [Finset.mem_filter, mem_summandPrefix, mem_summandTail]
    tauto
  have hs (T : Set ℕ) : (summandPrefix T X).filter (fun a => a ≤ lo) = summandPrefix T lo := by
    ext a
    simp only [Finset.mem_filter, mem_summandPrefix]
    constructor
    · rintro ⟨⟨ha, _⟩, hh⟩; exact ⟨ha, hh⟩
    · rintro ⟨ha, hh⟩; exact ⟨⟨ha, hh.trans hlo⟩, hh⟩
  simpa only [ht, hs] using pair_sum_filter_error (summandPrefix A X) (summandPrefix B X)
    lo W M hM (fun a _ b _ => hW (a + b))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmallEndpointBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical cost of the removed small endpoints -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

 theorem sqrt_log_prefix_bound (C T : ℝ) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (lo : ℕ) (hlo : 1 ≤ lo) (hupper : (lo : ℝ) ≤ Real.exp (9 * T / 10)) :
    C * Real.sqrt (lo : ℝ) * Real.log (lo : ℝ) ^ 2 ≤ C * Real.exp (9 * T / 20) * T ^ 2 := by
  have hlo1 : (1 : ℝ) ≤ lo := by exact_mod_cast hlo
  have hlop : (0 : ℝ) < lo := by linarith
  have hlog0 := Real.log_nonneg hlo1
  have hlog : Real.log (lo : ℝ) ≤ T := by
    have hh := Real.log_le_log hlop hupper
    rw [Real.log_exp] at hh
    linarith
  have hsqrt : Real.sqrt (lo : ℝ) ≤ Real.exp (9 * T / 20) := by
    have hh := Real.sqrt_le_sqrt hupper
    have he : Real.exp (9 * T / 10) = Real.exp (9 * T / 20) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rwa [he, Real.sqrt_sq (Real.exp_nonneg _)] at hh
  exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hC)
    (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _) (by positivity)

 theorem endpoint_count_product_bound (C T a b u v : ℝ) (hC : 0 ≤ C)
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (haU : a ≤ C * Real.exp (9 * T / 20) * T ^ 2)
    (hbU : b ≤ C * Real.exp (9 * T / 20) * T ^ 2)
    (huU : u ≤ C * Real.exp (T / 2) * T ^ 2)
    (hvU : v ≤ C * Real.exp (T / 2) * T ^ 2) :
    a * v + u * b ≤ 2 * C ^ 2 * Real.exp (19 * T / 20) * T ^ 4 := by
  have h₁ := mul_le_mul haU hvU hv (by positivity)
  have h₂ := mul_le_mul huU hbU hb (by positivity)
  calc
    _ ≤ (C * Real.exp (9 * T / 20) * T ^ 2) * (C * Real.exp (T / 2) * T ^ 2) +
        (C * Real.exp (T / 2) * T ^ 2) * (C * Real.exp (9 * T / 20) * T ^ 2) :=
      add_le_add h₁ h₂
    _ = 2 * C ^ 2 * (Real.exp (9 * T / 20) * Real.exp (T / 2)) * T ^ 4 := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 3
      ring

 theorem eventual_small_endpoint_error (C D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      2 * C ^ 2 * Real.exp ((24 / 25 : ℝ) * Real.exp L) * Real.exp (5 * L) ≤
        Real.exp (Real.exp L) * Real.exp (-D * L) := by
  have hs := ((isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 1 by norm_num)).const_mul_left
    (25 * |D + 6|)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hs, Real.tendsto_exp_atTop.eventually_ge_atTop (2 * C ^ 2),
    eventually_ge_atTop (0 : ℝ)] with L hsmall hC hL
  have hl : 25 * |D + 6| * L ≤ Real.exp L := by
    simpa only [pow_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 25 * |D + 6| * L), abs_of_pos (Real.exp_pos _)] using hsmall
  calc
    _ ≤ Real.exp L * Real.exp ((24 / 25 : ℝ) * Real.exp L) * Real.exp (5 * L) := by
      gcongr
    _ = Real.exp ((24 / 25 : ℝ) * Real.exp L + 6 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.exp L - D * L) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (le_abs_self (D + 6)) hL
      linarith
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ActualSmallEndpointBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-endpoint error for the original summand prefixes -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

 theorem EventuallyPrimeSumset.small_endpoint_budget (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ M : ℝ, 0 ≤ M → M ≤ Real.exp (Real.exp L / 100) →
      Real.log X * M *
        (((summandPrefix A (summandTailCutoff (Real.exp L))).card : ℝ) *
            (summandPrefix B X).card +
          ((summandPrefix A X).card : ℝ) *
            (summandPrefix B (summandTailCutoff (Real.exp L))).card) ≤
        (X : ℝ) * Real.exp (-D * L) := by
  obtain ⟨a, C, _, hC, N₀, hcounts⟩ := hsize A B hA hB h
  let K := max N₀ 2
  filter_upwards [eventual_small_endpoint_error C D,
    Real.tendsto_exp_atTop.eventually_ge_atTop (2 * ((K : ℝ) + 2)),
    eventually_ge_atTop (1 : ℝ)] with L herror hbig hL
  intro X hX M hM hMupper
  let T := Real.exp L
  let lo := summandTailCutoff T
  have hT : 1 ≤ T := Real.one_le_exp (by linarith)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hKexp : (K : ℝ) ≤ Real.exp (9 * T / 10) := by
    have he := Real.add_one_le_exp (9 * T / 10)
    change 2 * ((K : ℝ) + 2) ≤ T at hbig
    linarith
  have hKlo : K ≤ lo := Nat.le_floor hKexp
  have hloUpper : (lo : ℝ) ≤ Real.exp (9 * T / 10) := Nat.floor_le (Real.exp_nonneg _)
  have hloX : lo ≤ X := by
    have he : Real.exp (9 * T / 10) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
    have hh := hloUpper.trans he
    change (X : ℝ) = Real.exp T at hX
    rw [← hX] at hh
    exact_mod_cast hh
  have hNlo : N₀ ≤ lo := (le_max_left _ _).trans hKlo
  have h2lo : 2 ≤ lo := (le_max_right _ _).trans hKlo
  have hcntlo := hcounts lo hNlo h2lo
  have hcntX := hcounts X (hNlo.trans hloX) (h2lo.trans hloX)
  have hsqrtX : Real.sqrt (X : ℝ) = Real.exp (T / 2) := by
    rw [hX]
    change Real.sqrt (Real.exp T) = _
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have hlogX : Real.log X = T := by rw [hX, Real.log_exp]
  have hfullA : ((summandPrefix A X).card : ℝ) ≤ C * Real.exp (T / 2) * T ^ 2 := by
    simpa only [hsqrtX, hlogX] using hcntX.2.1
  have hfullB : ((summandPrefix B X).card : ℝ) ≤ C * Real.exp (T / 2) * T ^ 2 := by
    simpa only [hsqrtX, hlogX] using hcntX.2.2.2
  have hsmallA := hcntlo.2.1.trans (sqrt_log_prefix_bound C T hC.le hT lo (by omega) hloUpper)
  have hsmallB := hcntlo.2.2.2.trans (sqrt_log_prefix_bound C T hC.le hT lo (by omega) hloUpper)
  have hcard := endpoint_count_product_bound C T
    (summandPrefix A lo).card (summandPrefix B lo).card
    (summandPrefix A X).card (summandPrefix B X).card hC.le
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hsmallA hsmallB hfullA hfullB
  change M ≤ Real.exp (T / 100) at hMupper
  rw [hlogX]
  calc
    _ ≤ T * Real.exp (T / 100) * (2 * C ^ 2 * Real.exp (19 * T / 20) * T ^ 4) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hMupper (by positivity)
      · exact hcard
      · positivity
      · positivity
    _ = 2 * C ^ 2 * Real.exp ((24 / 25 : ℝ) * T) * Real.exp (5 * L) := by
      have hpow : T ^ 5 = Real.exp (5 * L) := by
        dsimp [T]
        rw [← Real.exp_nat_mul]
        norm_num
      have he : Real.exp (T / 100) * Real.exp (19 * T / 20) =
          Real.exp ((24 / 25 : ℝ) * T) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = 2 * C ^ 2 * (Real.exp (T / 100) * Real.exp (19 * T / 20)) * T ^ 5 := by ring
        _ = _ := by rw [he, hpow]
    _ ≤ _ := by simpa only [hX] using herror

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SparseTailCoverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full prime coverage forces a large sparse weight on the actual tails -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

 theorem EventuallyPrimeSumset.sparse_tail_coverage_oai
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) (C : ℝ) (hC : 1000 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
        (S : ∀ i, Finset (ZMod (p i))),
        Pairwise (fun i j => (p i).Coprime (p j)) →
        (∀ i, (S i).Nonempty) → (∀ i, (S i).card < p i) →
        (∀ i, (100 : ℝ) ≤ p i) →
        (∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i)) →
        (∀ i, residueDensity (S i) ≤ 2 / 3) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 1000000 →
        (∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2) →
        (∑ i, (p i : ℝ)⁻¹) ≤ L →
        (∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) →
        (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
        let U := ∏ i, sparseKernelUnitFactor (p i)
          (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
        0 < U ∧ ((∫ t : ℝ, primeMeanTest t) / 8) * U * X ≤
          Real.log X * ∑ a ∈ summandTail A (summandTailCutoff (Real.exp L)) X,
            ∑ b ∈ summandTail B (summandTailCutoff (Real.exp L)) X,
              sparseSubsetWeight p S (sparseTruncationDegree C L)
                (fun i => ((a + b : ℕ) : ZMod (p i))) := by
  obtain ⟨N, hcoverage⟩ := h.smooth_coverage
  have hlim : Tendsto (fun L : ℝ => Real.exp (Real.exp L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp Real.tendsto_exp_atTop
  filter_upwards [sparseWeightedPrimeSum_lower Z hD hR P hPNT C hC,
    h.small_endpoint_budget hsize hA hB 10,
    eventual_sparse_weight_subpower C (1 / 100) (by linarith) (by norm_num),
    eventual_sparse_prime_error_margin (∫ t : ℝ, primeMeanTest t) primeMeanTest_integral_pos,
    hlim.eventually_ge_atTop (2 * (N : ℝ)), eventually_ge_atTop (1 : ℝ)]
    with L hprime hdelete hweight hmargin hlarge hL
  obtain ⟨exception, he⟩ := hprime
  refine ⟨exception, ?_⟩
  intro X hX n p hp hprod S hc hS hSp hp100 hlo hhi ε hε hεsmall hL1 hH hlog havoid U
  obtain ⟨hU, hUlow, hprime⟩ := he n p S hc hS hSp hp100 hlo hhi ε hε hεsmall hL1 hH hlog havoid
  refine ⟨hU, ?_⟩
  let K := sparseTruncationDegree C L
  let lo := summandTailCutoff (Real.exp L)
  let W := fun q : ℕ => sparseSubsetWeight p S K (fun i => (q : ZMod (p i)))
  let M : ℝ := ((K + 1 : ℝ) * (n + 1 : ℝ) ^ K) ^ 2
  have hW (q : ℕ) : W q ≤ M := sparseSubsetWeight_uniform_bound p S K _
  have hWpos (q : ℕ) : 0 ≤ W q := sparseSubsetWeight_nonneg p S K _
  have hX1 : 1 ≤ (X : ℝ) := by rw [hX]; exact Real.one_le_exp (Real.exp_nonneg _)
  have hlog0 := Real.log_nonneg hX1
  have hcov := hcoverage X hX1 (by simpa only [hX] using hlarge) W hWpos
  have hMw : M ≤ Real.exp (Real.exp L / 100) := by
    simpa only [M, K, div_eq_mul_inv, one_mul, mul_comm] using hweight n (sparse_prime_family_card p hc L hlog)
  have hdel := hdelete X hX M (sq_nonneg _) hMw
  have hloX : lo ≤ X := by
    have he : (lo : ℝ) ≤ Real.exp (9 * Real.exp L / 10) := Nat.floor_le (Real.exp_nonneg _)
    have hle : Real.exp (9 * Real.exp L / 10) ≤ Real.exp (Real.exp L) :=
      Real.exp_le_exp.mpr (by linarith [Real.exp_pos L])
    have hh := he.trans hle
    rw [← hX] at hh
    exact_mod_cast hh
  have hsplit := mul_le_mul_of_nonneg_left
    (prefix_pair_sum_le_tail A B lo X hloX W M (sq_nonneg _) hW) hlog0
  rw [mul_add] at hsplit
  have hecost : (X : ℝ) * Real.exp (-10 * L) ≤
      ((∫ t : ℝ, primeMeanTest t) / 8) * U * X := by
    have hmar : Real.exp (-10 * L) ≤ ((∫ t : ℝ, primeMeanTest t) / 8) * U := by
      have hpos : 0 ≤ (∫ t : ℝ, primeMeanTest t) / 4 :=
        div_nonneg primeMeanTest_integral_pos.le (by norm_num)
      have hh := mul_le_mul_of_nonneg_left hUlow hpos
      linarith
    have hh := mul_le_mul_of_nonneg_right hmar (Nat.cast_nonneg X)
    nlinarith only [hh]
  have hprime' : ((∫ t : ℝ, primeMeanTest t) / 4) * U * X ≤
      ∑ q ∈ (Finset.Ioc 0 ⌊(X : ℝ)⌋₊).filter Nat.Prime,
        Real.log q * W q * primeMeanTest (q / X) := by
    simpa only [← hX, sparseWeightedPrimeSum] using hprime
  have herr : Real.log X * (M *
      (((summandPrefix A lo).card : ℝ) * (summandPrefix B X).card +
        ((summandPrefix A X).card : ℝ) * (summandPrefix B lo).card)) ≤
      ((∫ t : ℝ, primeMeanTest t) / 8) * U * X := by
    have hh : Real.log X * (M *
        (((summandPrefix A lo).card : ℝ) * (summandPrefix B X).card +
          ((summandPrefix A X).card : ℝ) * (summandPrefix B lo).card)) ≤
        (X : ℝ) * Real.exp (-10 * L) := by
      simpa only [lo, mul_assoc] using hdel
    exact hh.trans hecost
  change _ ≤ Real.log X * ∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X, W (a + b)
  simp only [Nat.floor_natCast] at hcov hprime'
  linarith

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage_oai := @OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage_oai
