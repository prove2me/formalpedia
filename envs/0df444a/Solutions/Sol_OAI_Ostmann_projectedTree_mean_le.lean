-- Prove2me | solution 1 for OAI.Ostmann.projectedTree_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:43:10.111663+00:00
-- url     : https://prove2.me/submissions/506cae6d-195c-402f-af32-af3e393e1998

import Mathlib
import Definitions.Def_OAIQ095D007

section
-- module Solutions.OAIQ095_OS.Compat
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

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

/-- Additive Parseval with the manuscript's probability convention. -/
theorem additiveFourier_parseval {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2) =
      (p : ℝ)⁻¹ * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  rw [additiveFourier_energy f]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem additiveFourier_sub {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => f x - g x) a = additiveFourier f a - additiveFourier g a := by
  simp only [additiveFourier_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem additiveFourier_const {p : ℕ} [NeZero p] (c : ℂ) (a : ZMod p) :
    additiveFourier (fun _ : ZMod p => c) a = if a = 0 then c else 0 := by
  classical
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [additiveFourier_apply]
  simp only [← mul_neg, ← Finset.mul_sum]
  rw [AddChar.sum_mulShift (-a) (ZMod.isPrimitive_stdAddChar p)]
  simp only [ZMod.card, neg_eq_zero]
  by_cases ha : a = 0
  · simp only [ha, ite_true, if_true]
    field_simp
  · simp only [ha, ite_false, if_false, Nat.cast_zero, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarePullback
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
private theorem square_fiber_card_le_two {ι K : Type*} [Field K] [DecidableEq K]
    (s : Finset ι) (f : ι → K) (hf : Function.Injective f) (y : K) :
    (s.filter fun x => f x ^ 2 = y).card ≤ 2 := by
  classical
  let t := s.filter fun x => f x ^ 2 = y
  by_cases ht : t.Nonempty
  · obtain ⟨a, ha⟩ := ht
    have haeq : f a ^ 2 = y := (Finset.mem_filter.mp ha).2
    have hsub : t.image f ⊆ {f a, -f a} := by
      intro z hz
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      have hbeq : f b ^ 2 = y := (Finset.mem_filter.mp hb).2
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        (sq_eq_sq_iff_eq_or_eq_neg.mp (hbeq.trans haeq.symm))
    calc
      t.card = (t.image f).card := (Finset.card_image_of_injective t hf).symm
      _ ≤ ({f a, -f a} : Finset K).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · have : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change t.card ≤ 2
    simp only [this, Finset.card_empty, Nat.zero_le]

/-- Squaring has at most two preimages among the units of a prime field. -/
theorem unit_square_fiber_card_le_two {p : ℕ} [Fact p.Prime]
    (s : Finset (ZMod p)ˣ) (u : (ZMod p)ˣ) :
    (s.filter fun x => x ^ 2 = u).card ≤ 2 := by
  classical
  have heq : (s.filter fun x => x ^ 2 = u) =
      s.filter (fun x : (ZMod p)ˣ => (x : ZMod p) ^ 2 = (u : ZMod p)) := by
    ext x
    simp only [Finset.mem_filter, ← Units.val_pow_eq_pow_val, Units.val_inj]
  rw [heq]
  exact square_fiber_card_le_two s (fun x : (ZMod p)ˣ => (x : ZMod p))
    Units.val_injective (u : ZMod p)

/-- The same two-point bound applies on the character group of a prime field. -/
theorem mulChar_square_fiber_card_le_two {p : ℕ} [Fact p.Prime]
    (s : Finset (MulChar (ZMod p) ℂ)) (ρ : MulChar (ZMod p) ℂ) :
    (s.filter fun χ => χ ^ 2 = ρ).card ≤ 2 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hinj : Function.Injective (fun χ : MulChar (ZMod p) ℂ => χ g) := by
    intro χ ψ h
    exact (MulChar.eq_iff hg χ ψ).mpr h
  have hsub : (s.filter fun χ => χ ^ 2 = ρ) ⊆
      s.filter (fun χ => χ g ^ 2 = ρ g) := by
    intro χ hχ
    obtain ⟨hs, hχ⟩ := Finset.mem_filter.mp hχ
    refine Finset.mem_filter.mpr ⟨hs, ?_⟩
    simpa only [MulChar.pow_apply_coe] using congrArg (fun ψ : MulChar (ZMod p) ℂ => ψ g) hχ
  exact (Finset.card_le_card hsub).trans (square_fiber_card_le_two s _ hinj _)

private theorem norm_sq_sum_le_two {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (hs : s.card ≤ 2) : ‖∑ x ∈ s, c x‖ ^ 2 ≤ 2 * ∑ x ∈ s, ‖c x‖ ^ 2 := by
  have hn : 0 ≤ ∑ x ∈ s, ‖c x‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsum : ‖∑ x ∈ s, c x‖ ≤ ∑ x ∈ s, ‖c x‖ := norm_sum_le _ _
  have hsq : ‖∑ x ∈ s, c x‖ ^ 2 ≤ (∑ x ∈ s, ‖c x‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ x ∈ s, c x)]
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun x => ‖c x‖)
  have hcard : (s.card : ℝ) ≤ 2 := by exact_mod_cast hs
  have hnn : 0 ≤ ∑ x ∈ s, ‖c x‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact hsq.trans (hcs.trans (mul_le_mul_of_nonneg_right hcard hnn))

/-- A multiplicative character has modulus one at each unit. -/
theorem norm_mulChar_unit {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (u : (ZMod p)ˣ) : ‖χ u‖ = 1 := by
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

/-- The two surviving Mellin coefficients in a square pullback satisfy the
factor-two estimate, including their unit phases. -/
theorem square_pullback_coefficients {p : ℕ} [Fact p.Prime]
    (s : Finset (MulChar (ZMod p) ℂ)) (c : MulChar (ZMod p) ℂ → ℂ)
    (K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    ‖∑ χ ∈ s.filter (fun χ => χ ^ 2 = ρ), c χ * χ K‖ ^ 2 ≤
      2 * ∑ χ ∈ s.filter (fun χ => χ ^ 2 = ρ), ‖c χ‖ ^ 2 := by
  have h := norm_sq_sum_le_two (s.filter fun χ => χ ^ 2 = ρ)
    (fun χ => c χ * χ K) (mulChar_square_fiber_card_le_two s ρ)
  simpa only [norm_mul, norm_mulChar_unit, mul_one] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineFibers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonidentity affine-map fibers

The finite-field representation count used immediately before equation
`tree-affine-coefficient-norm`: every nonidentity affine map arising from
`U_r^* U_s` has at most two representations.
-/

namespace Ostmann

/-- The ratio-coordinate translation equals the manuscript's `s - s²/r`. -/
theorem affineParameters_translation {p : ℕ} [Fact p.Prime] (r s : (ZMod p)ˣ) :
    (affineParameters r s).2 = (s : ZMod p) - (s : ZMod p) ^ 2 / (r : ZMod p) := by
  simp only [affineParameters, Units.val_div_eq_div_val]
  field_simp

private theorem sub_sq_ne_zero {p : ℕ} [Fact p.Prime]
    (z : (ZMod p)ˣ) (hz : z ≠ 1) : (z : ZMod p) - (z : ZMod p) ^ 2 ≠ 0 := by
  intro h
  have hprod : (z : ZMod p) * (1 - (z : ZMod p)) = 0 := by
    calc
      (z : ZMod p) * (1 - (z : ZMod p)) = (z : ZMod p) - (z : ZMod p) ^ 2 := by ring
      _ = 0 := h
  rcases mul_eq_zero.mp hprod with hzero | hone
  · exact Units.ne_zero z hzero
  · exact hz (Units.ext (sub_eq_zero.mp hone).symm)

private theorem ratio_ne_one_of_nonidentity {p : ℕ} (r s : (ZMod p)ˣ)
    (h : affineParameters r s ≠ (1, 0)) : s / r ≠ 1 := by
  intro heq
  apply h
  simp only [affineParameters, heq, one_pow, Units.val_one, sub_self, mul_zero]

/-- The ratio determines both unit parameters once a nonidentity affine map
has been fixed. -/
theorem affineParameters_ratio_injective {p : ℕ} [Fact p.Prime]
    {r s r' s' : (ZMod p)ˣ}
    (hnon : affineParameters r s ≠ (1, 0))
    (hmap : affineParameters r s = affineParameters r' s')
    (hratio : s / r = s' / r') : r = r' ∧ s = s' := by
  have hz := ratio_ne_one_of_nonidentity r s hnon
  have hfactor := sub_sq_ne_zero (s / r) hz
  have htrans := congrArg Prod.snd hmap
  change (r : ZMod p) * (((s / r : (ZMod p)ˣ) : ZMod p) -
      ((s / r : (ZMod p)ˣ) : ZMod p) ^ 2) =
    (r' : ZMod p) * (((s' / r' : (ZMod p)ˣ) : ZMod p) -
      ((s' / r' : (ZMod p)ˣ) : ZMod p) ^ 2) at htrans
  rw [← hratio] at htrans
  have hr : r = r' := Units.ext (mul_right_cancel₀ hfactor htrans)
  refine ⟨hr, ?_⟩
  subst r'
  have := congrArg (fun u : (ZMod p)ˣ => u * r) hratio
  simpa only [div_mul_cancel] using this

/-- Every nonidentity affine map has at most two ordered unit representations. -/
theorem affineParameters_fiber_card_le_two {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (b : ZMod p) (hnon : (a, b) ≠ (1, 0)) :
    ((Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
      (fun rs => affineParameters rs.1 rs.2 = (a, b))).card ≤ 2 := by
  classical
  let S := (Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
    (fun rs => affineParameters rs.1 rs.2 = (a, b))
  let T := (Finset.univ : Finset (ZMod p)ˣ).filter (fun z => z ^ 2 = a)
  have hmaps : Set.MapsTo (fun rs : (ZMod p)ˣ × (ZMod p)ˣ => rs.2 / rs.1) S T := by
    intro rs hrs
    have hmap := (Finset.mem_filter.mp hrs).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact congrArg Prod.fst hmap
  have hinj : (S : Set ((ZMod p)ˣ × (ZMod p)ˣ)).InjOn
      (fun rs => rs.2 / rs.1) := by
    intro rs hrs uv huv hratio
    have hrs' := (Finset.mem_filter.mp hrs).2
    have huv' := (Finset.mem_filter.mp huv).2
    have hn : affineParameters rs.1 rs.2 ≠ (1, 0) := by simpa only [hrs'] using hnon
    have h := affineParameters_ratio_injective hn (hrs'.trans huv'.symm) hratio
    exact Prod.ext h.1 h.2
  exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans
    (unit_square_fiber_card_le_two Finset.univ a)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TestFunctions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transfer from collision distance to test functions

The tests need only a bounded squared norm, not a pointwise bound. This is
the Cauchy--Schwarz estimate immediately following Lemma 2.5 in the paper.
-/

namespace Ostmann

open scoped BigOperators

theorem complex_weighted_sum_sq {α : Type*} (s : Finset α)
    (w : α → ℝ) (f : α → ℂ) :
    ‖∑ r ∈ s, (w r : ℂ) * f r‖ ^ 2 ≤
      (∑ r ∈ s, w r ^ 2) * ∑ r ∈ s, ‖f r‖ ^ 2 := by
  have hnorm : ‖∑ r ∈ s, (w r : ℂ) * f r‖ ≤ ∑ r ∈ s, |w r| * ‖f r‖ := by
    calc
      _ ≤ ∑ r ∈ s, ‖(w r : ℂ) * f r‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnonneg : 0 ≤ ∑ r ∈ s, |w r| * ‖f r‖ :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun r => |w r|) (fun r => ‖f r‖)
  simp only [sq_abs] at hCS
  nlinarith [norm_nonneg (∑ r ∈ s, (w r : ℂ) * f r)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The affine coefficient array

The identity fiber is diagonal, and all other fibers have size at most two.
These facts give the coefficient-square estimate in equation
`tree-affine-coefficient-norm` without a pointwise bound on the function.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem norm_sum_sq_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := by
  simpa using complex_weighted_sum_sq s (fun _ => 1) f

theorem affineParameters_eq_identity_iff {p : ℕ} [Fact p.Prime]
    (r s : (ZMod p)ˣ) : affineParameters r s = (1, 0) ↔ r = s := by
  constructor
  · intro h
    have hsquare : (s / r) ^ 2 = 1 := congrArg Prod.fst h
    have htrans := congrArg Prod.snd h
    change (r : ZMod p) * (((s / r : (ZMod p)ˣ) : ZMod p) -
      ((s / r : (ZMod p)ˣ) : ZMod p) ^ 2) = 0 at htrans
    rw [← Units.val_pow_eq_pow_val, hsquare, Units.val_one] at htrans
    have hz : (s / r : (ZMod p)ˣ) = 1 :=
      Units.ext (sub_eq_zero.mp ((mul_eq_zero.mp htrans).resolve_left (Units.ne_zero r)))
    exact (div_eq_one.mp hz).symm
  · rintro rfl
    simp [affineParameters]

theorem affineCoefficientSum_identity {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) :
    affineCoefficientSum G (1, 0) = ∑ r : (ZMod p)ˣ, conj (G r) * G r := by
  classical
  simp only [affineCoefficientSum, Finset.sum_filter, affineParameters_eq_identity_iff]
  rw [Fintype.sum_prod_type]
  simp

theorem affineCoefficientSum_nonidentity_bound {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) (ab : (ZMod p)ˣ × ZMod p) (hab : ab ≠ (1, 0)) :
    ‖affineCoefficientSum G ab‖ ^ 2 ≤
      2 * ∑ rs ∈ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
        (fun rs => affineParameters rs.1 rs.2 = ab),
        ‖G rs.1‖ ^ 2 * ‖G rs.2‖ ^ 2 := by
  classical
  have hc : (((Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
      (fun rs => affineParameters rs.1 rs.2 = ab)).card : ℝ) ≤ 2 := by
    exact_mod_cast affineParameters_fiber_card_le_two ab.1 ab.2 hab
  have hn := norm_sum_sq_le_card_mul
    ((Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
      (fun rs => affineParameters rs.1 rs.2 = ab))
    (fun rs => conj (G rs.1) * G rs.2)
  simp only [norm_mul, Complex.norm_conj, mul_pow] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hc
    (Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem affineCoefficientSum_sq_sum {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) :
    (∑ ab : (ZMod p)ˣ × ZMod p, ‖affineCoefficientSum G ab‖ ^ 2) ≤
      3 * (∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2) ^ 2 := by
  classical
  let S : ℝ := ∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2
  let w : (ZMod p)ˣ × (ZMod p)ˣ → ℝ := fun rs => ‖G rs.1‖ ^ 2 * ‖G rs.2‖ ^ 2
  let F : (ZMod p)ˣ × ZMod p → ℝ := fun ab =>
    ∑ rs ∈ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
      (fun rs => affineParameters rs.1 rs.2 = ab), w rs
  have hF : ∀ ab, 0 ≤ F ab := fun ab =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have htotal : ∑ ab, F ab = S ^ 2 := by
    simp only [F, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
    rw [Fintype.sum_prod_type]
    simp only [w]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    exact (pow_two S).symm
  have hid : ‖affineCoefficientSum G (1, 0)‖ ^ 2 = S ^ 2 := by
    rw [affineCoefficientSum_identity]
    have heq : (∑ r : (ZMod p)ˣ, conj (G r) * G r) = (S : ℂ) := by
      simp only [S, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
    rw [heq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1, 0)), hid]
  have hrest : (∑ ab ∈ (Finset.univ : Finset ((ZMod p)ˣ × ZMod p)).erase (1, 0),
      ‖affineCoefficientSum G ab‖ ^ 2) ≤ 2 * S ^ 2 := by
    calc
      _ ≤ ∑ ab ∈ (Finset.univ : Finset ((ZMod p)ˣ × ZMod p)).erase (1, 0),
          2 * F ab := by
        apply Finset.sum_le_sum
        intro ab hab
        exact affineCoefficientSum_nonidentity_bound G ab (Finset.mem_erase.mp hab).1
      _ ≤ ∑ ab, 2 * F ab := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun ab _ _ => mul_nonneg (by norm_num) (hF ab))
      _ = 2 * S ^ 2 := by rw [← Finset.mul_sum, htotal]
  change _ ≤ 3 * S ^ 2
  linarith

/-- Equation `tree-affine-coefficient-norm`, with the probability `L²` hypothesis. -/
theorem affineCoefficient_sq_sum_le {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) (hG : (∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2) ≤ (p : ℝ)) :
    (∑ ab : (ZMod p)ˣ × ZMod p, ‖affineCoefficient G ab‖ ^ 2) ≤
      3 / (p : ℝ) ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hG₀ : 0 ≤ ∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ = (∑ ab : (ZMod p)ˣ × ZMod p, ‖affineCoefficientSum G ab‖ ^ 2) /
        ((p : ℝ) ^ 2) ^ 2 := by
      simp only [affineCoefficient, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (p : ℝ)), div_pow,
        Finset.sum_div]
    _ ≤ (3 * (∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2) ^ 2) / ((p : ℝ) ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right (affineCoefficientSum_sq_sum G) (sq_nonneg _)
    _ ≤ (3 * (p : ℝ) ^ 2) / ((p : ℝ) ^ 2) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hG₀ hp.le).mpr hG) (by norm_num)
    _ = 3 / (p : ℝ) ^ 2 := by field_simp [ne_of_gt hp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The affine action in the Fourier basis

On nonzero additive frequencies the affine action is a matrix whose entries
are additive character sums. Parseval bounds its squared matrix norm by
`p` times the coefficient energy. This is the finite matrix estimate in
the proof of the uniform Mellin bound in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveCharacterSum_eq {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (ξ : ZMod p) :
    additiveCharacterSum f ξ = (p : ℂ) * additiveFourier f (-ξ) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [additiveFourier_apply, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  simp only [additiveCharacterSum, mul_neg, neg_neg, mul_comm ξ]

theorem additiveCharacterSum_energy {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ ξ : ZMod p, ‖additiveCharacterSum f ξ‖ ^ 2) =
      (p : ℝ) * ∑ b : ZMod p, ‖f b‖ ^ 2 := by
  simp_rw [additiveCharacterSum_eq, norm_mul, Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum]
  have hreindex : (∑ ξ : ZMod p, ‖additiveFourier f (-ξ)‖ ^ 2) =
      ∑ ξ : ZMod p, ‖additiveFourier f ξ‖ ^ 2 :=
    (Equiv.neg (ZMod p)).bijective.sum_comp (fun ξ => ‖additiveFourier f ξ‖ ^ 2)
  rw [hreindex, additiveFourier_parseval]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp [hp]

theorem additiveCharacterSum_unit_energy_le {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) :
    (∑ ξ : (ZMod p)ˣ, ‖additiveCharacterSum f ξ‖ ^ 2) ≤
      (p : ℝ) * ∑ b : ZMod p, ‖f b‖ ^ 2 := by
  classical
  rw [← additiveCharacterSum_energy]
  exact OAI.sum_le_sum_of_injOn (fun ξ : (ZMod p)ˣ => (ξ : ZMod p))
    Units.val_injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
    (fun _ _ _ => sq_nonneg _)

theorem affineFourierMatrix_energy_le {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) :
    (∑ η : (ZMod p)ˣ, ∑ ξ : (ZMod p)ˣ, ‖affineFourierMatrix c η ξ‖ ^ 2) ≤
      (p : ℝ) * ∑ ab : (ZMod p)ˣ × ZMod p, ‖c ab‖ ^ 2 := by
  classical
  have hreindex (ξ : (ZMod p)ˣ) :
      (∑ η : (ZMod p)ˣ, ‖affineFourierMatrix c η ξ‖ ^ 2) =
        ∑ a : (ZMod p)ˣ, ‖additiveCharacterSum (fun b => c (a, b)) ξ‖ ^ 2 := by
    calc
      _ = ∑ a : (ZMod p)ˣ, ‖affineFourierMatrix c (a * ξ) ξ‖ ^ 2 :=
        ((Equiv.mulRight ξ).bijective.sum_comp
          (fun η => ‖affineFourierMatrix c η ξ‖ ^ 2)).symm
      _ = _ := by simp only [affineFourierMatrix, mul_div_cancel_right]
  rw [Finset.sum_comm]
  simp_rw [hreindex]
  rw [Finset.sum_comm, Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => additiveCharacterSum_unit_energy_le (fun b => c (a, b)))

theorem complex_sum_mul_sq {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    ‖∑ j ∈ s, f j * g j‖ ^ 2 ≤
      (∑ j ∈ s, ‖f j‖ ^ 2) * ∑ j ∈ s, ‖g j‖ ^ 2 := by
  have hnorm : ‖∑ j ∈ s, f j * g j‖ ≤ ∑ j ∈ s, ‖f j‖ * ‖g j‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun j => f j * g j)
  have hn : 0 ≤ ∑ j ∈ s, ‖f j‖ * ‖g j‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖f j‖) (fun j => ‖g j‖)
  nlinarith [norm_nonneg (∑ j ∈ s, f j * g j)]

theorem finite_matrix_energy_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℂ) (v : κ → ℂ) :
    (∑ i : ι, ‖∑ j : κ, A i j * v j‖ ^ 2) ≤
      (∑ i : ι, ∑ j : κ, ‖A i j‖ ^ 2) * ∑ j : κ, ‖v j‖ ^ 2 := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => complex_sum_mul_sq Finset.univ (A i) v)

theorem affineFourier_action_energy_bound {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (v : (ZMod p)ˣ → ℂ) :
    (∑ η : (ZMod p)ˣ, ‖∑ ξ : (ZMod p)ˣ, affineFourierMatrix c η ξ * v ξ‖ ^ 2) ≤
      ((p : ℝ) * ∑ ab : (ZMod p)ˣ × ZMod p, ‖c ab‖ ^ 2) *
        ∑ ξ : (ZMod p)ˣ, ‖v ξ‖ ^ 2 := by
  exact (finite_matrix_energy_bound (affineFourierMatrix c) v).trans
    (mul_le_mul_of_nonneg_right (affineFourierMatrix_energy_le c)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Autocorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Additive autocorrelation

The probability-normalized Fourier transform of an autocorrelation is
the squared modulus of the original transform. This is the positivity
identity used for the bottom-pair coefficients in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_translation_sum {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (a y : ZMod p) :
    (∑ x : ZMod p, g (x - y) * ZMod.stdAddChar (-(x * a))) =
      ZMod.stdAddChar (-(y * a)) * ∑ z : ZMod p, g z * ZMod.stdAddChar (-(z * a)) := by
  calc
    _ = ∑ z : ZMod p, g ((z + y) - y) * ZMod.stdAddChar (-((z + y) * a)) :=
      ((Equiv.addRight y).bijective.sum_comp
        (fun x : ZMod p => g (x - y) * ZMod.stdAddChar (-(x * a)))).symm
    _ = _ := by
      simp only [add_sub_cancel_right, add_mul, neg_add, AddChar.map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

theorem additiveFourier_convolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (additiveConvolution f g) a =
      additiveFourier f a * additiveFourier g a := by
  simp only [additiveFourier_apply, additiveConvolution]
  calc
    _ = (p : ℂ)⁻¹ * (p : ℂ)⁻¹ *
        ∑ y : ZMod p, f y * ∑ x : ZMod p, g (x - y) * ZMod.stdAddChar (-(x * a)) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [additiveFourier_translation_sum]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      ring

theorem additiveFourier_reflected_conj {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => conj (f (-x))) a = conj (additiveFourier f a) := by
  rw [additiveFourier_apply, additiveFourier_apply]
  simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj, neg_neg]
  congr 1
  calc
    _ = ∑ y : ZMod p, conj (f (-(-y))) * ZMod.stdAddChar (-((-y) * a)) :=
      ((Equiv.neg (ZMod p)).bijective.sum_comp
        (fun x : ZMod p => conj (f (-x)) * ZMod.stdAddChar (-(x * a)))).symm
    _ = _ := by simp only [neg_neg, neg_mul]

theorem additiveAutocorrelation_eq_convolution {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) :
    additiveAutocorrelation f = additiveConvolution f (fun x => conj (f (-x))) := by
  funext d
  simp only [additiveAutocorrelation, additiveConvolution, neg_sub]

theorem additiveFourier_autocorrelation {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (additiveAutocorrelation f) a = (‖additiveFourier f a‖ ^ 2 : ℝ) := by
  rw [additiveAutocorrelation_eq_convolution, additiveFourier_convolution,
    additiveFourier_reflected_conj, Complex.mul_conj']
  norm_cast

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem additiveFourier_sum {p : ℕ} [NeZero p] {ι : Type*}
    (s : Finset ι) (F : ι → ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => ∑ i ∈ s, F i x) a =
      ∑ i ∈ s, additiveFourier (F i) a := by
  simp only [additiveFourier_apply, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem additiveFourier_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => c * f x) a = c * additiveFourier f a := by
  simp only [additiveFourier_apply, mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem additiveFourier_add_right {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (b a : ZMod p) :
    additiveFourier (fun x => f (x + b)) a =
      ZMod.stdAddChar (b * a) * additiveFourier f a := by
  have h := additiveFourier_translation_sum f a (-b)
  simp only [sub_neg_eq_add, neg_mul, neg_neg] at h
  simp only [additiveFourier_apply]
  rw [h]
  ring

theorem additiveFourier_unit_mul {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (u : (ZMod p)ˣ) (a : ZMod p) :
    additiveFourier (fun x => f ((u : ZMod p) * x)) a =
      additiveFourier f (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * a) := by
  exact congrArg (fun z : ℂ => (p : ℂ)⁻¹ * z) (ZMod.dft_comp_unitMul f u a)

theorem additiveFourier_affine_shift {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (u : (ZMod p)ˣ) (b a : ZMod p) :
    additiveFourier (fun x => f ((u : ZMod p) * x + b)) a =
      ZMod.stdAddChar (b * (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * a)) *
        additiveFourier f (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * a) := by
  rw [additiveFourier_unit_mul (fun x => f (x + b)), additiveFourier_add_right]

theorem additiveFourier_affineAction {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (f : ZMod p → ℂ) (η : (ZMod p)ˣ) :
    additiveFourier (affineAction c f) η =
      ∑ ξ : (ZMod p)ˣ, affineFourierMatrix c η ξ * additiveFourier f ξ := by
  classical
  have hfreq (ξ : (ZMod p)ˣ) :
      (((η / ξ)⁻¹ : (ZMod p)ˣ) : ZMod p) * (η : ZMod p) = (ξ : ZMod p) := by
    rw [← Units.val_mul]
    congr 1
    simp [div_eq_mul_inv, mul_assoc]
  unfold affineAction
  simp only [additiveFourier_sum, additiveFourier_const_mul,
    additiveFourier_affine_shift]
  calc
    _ = ∑ ξ : (ZMod p)ˣ, ∑ b : ZMod p, c (η / ξ, b) *
        (ZMod.stdAddChar (b * ((((η / ξ)⁻¹ : (ZMod p)ˣ) : ZMod p) * (η : ZMod p))) *
          additiveFourier f ((((η / ξ)⁻¹ : (ZMod p)ˣ) : ZMod p) * (η : ZMod p))) := by
      exact (((Equiv.inv (ZMod p)ˣ).trans (Equiv.mulLeft η)).bijective.sum_comp
        (fun a : (ZMod p)ˣ => ∑ b : ZMod p, c (a, b) *
          (ZMod.stdAddChar (b * (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (η : ZMod p))) *
            additiveFourier f (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (η : ZMod p))))).symm
    _ = _ := by
      simp_rw [hfreq]
      apply Finset.sum_congr rfl
      intro ξ _
      simp only [affineFourierMatrix, additiveCharacterSum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_comm b (ξ : ZMod p)]
      ring

theorem additiveFourier_affineAction_zero {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (f : ZMod p → ℂ)
    (hf : additiveFourier f 0 = 0) :
    additiveFourier (affineAction c f) 0 = 0 := by
  unfold affineAction
  simp only [additiveFourier_sum, additiveFourier_const_mul,
    additiveFourier_affine_shift, mul_zero, AddChar.map_zero_eq_one, hf,
    Finset.sum_const_zero]

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

/-- The affine action on mean-zero functions, in counting-measure squared norm. -/
theorem affineAction_energy_bound {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (f : ZMod p → ℂ)
    (hf : additiveFourier f 0 = 0) :
    (∑ t : ZMod p, ‖affineAction c f t‖ ^ 2) ≤
      ((p : ℝ) * ∑ ab : (ZMod p)ˣ × ZMod p, ‖c ab‖ ^ 2) *
        ∑ t : ZMod p, ‖f t‖ ^ 2 := by
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hout := sum_units_eq_sum_of_zero
    (fun a : ZMod p => ‖additiveFourier (affineAction c f) a‖ ^ 2)
    (by rw [additiveFourier_affineAction_zero c f hf, norm_zero, zero_pow (by decide)])
  have hin := sum_units_eq_sum_of_zero (fun a : ZMod p => ‖additiveFourier f a‖ ^ 2)
    (by rw [hf, norm_zero, zero_pow (by decide)])
  calc
    _ = (p : ℝ) * ∑ η : (ZMod p)ˣ,
        ‖∑ ξ : (ZMod p)ˣ, affineFourierMatrix c η ξ * additiveFourier f ξ‖ ^ 2 := by
      rw [additiveFourier_energy, ← hout]
      simp_rw [additiveFourier_affineAction]
    _ ≤ (p : ℝ) * (((p : ℝ) * ∑ ab : (ZMod p)ˣ × ZMod p, ‖c ab‖ ^ 2) *
        ∑ ξ : (ZMod p)ˣ, ‖additiveFourier f ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (affineFourier_action_energy_bound c (fun ξ => additiveFourier f ξ)) hp
    _ = _ := by rw [hin, additiveFourier_energy f]; ring

/-- The coefficient array arising from `T* T` has squared action norm at most `3/p`. -/
theorem affineAction_collected_energy_bound {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) (hG : (∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2) ≤ (p : ℝ))
    (f : ZMod p → ℂ) (hf : additiveFourier f 0 = 0) :
    (∑ t : ZMod p, ‖affineAction (affineCoefficient G) f t‖ ^ 2) ≤
      (3 / (p : ℝ)) * ∑ t : ZMod p, ‖f t‖ ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  refine (affineAction_energy_bound (affineCoefficient G) f hf).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ (p : ℝ) * (3 / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (affineCoefficient_sq_sum_le G hG) hp.le
    _ = 3 / (p : ℝ) := by field_simp [ne_of_gt hp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineOperator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The weighted affine averaging operator

This is the operator in equation `tree-affine-coefficient`, together with
its adjoint. Its adjoint square is the affine action whose coefficient
energy is bounded in `AffineCoefficients`.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem affineGenerator_comp_inv {p : ℕ} [Fact p.Prime]
    (r s : (ZMod p)ˣ) (t : ZMod p) :
    affineGenerator s (affineGeneratorInv r t) =
      ((affineParameters r s).1 : ZMod p) * t + (affineParameters r s).2 := by
  rw [affineParameters_translation]
  simp only [affineGenerator, affineGeneratorInv, affineParameters,
    Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]
  field_simp
  ring

theorem affineGenerator_inner_reindex {p : ℕ} [Fact p.Prime]
    (r : (ZMod p)ˣ) (F H : ZMod p → ℂ) :
    (∑ t : ZMod p, conj (F (affineGenerator r t)) * H t) =
      ∑ t : ZMod p, conj (F t) * H (affineGeneratorInv r t) := by
  have h := ((affineGeneratorEquiv r).symm.bijective.sum_comp
    (fun t : ZMod p => conj (F (affineGenerator r t)) * H t)).symm
  have hinv (t : ZMod p) : affineGenerator r (affineGeneratorInv r t) = t :=
    (affineGeneratorEquiv r).apply_symm_apply t
  change (∑ t : ZMod p, conj (F (affineGenerator r t)) * H t) =
    ∑ t : ZMod p, conj (F (affineGenerator r (affineGeneratorInv r t))) *
      H (affineGeneratorInv r t) at h
  simpa only [hinv] using h

theorem affineAverage_adjoint_identity {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F H : ZMod p → ℂ) :
    (∑ t : ZMod p, conj (affineAverage W F t) * H t) =
      ∑ t : ZMod p, conj (F t) * affineAverageAdjoint W H t := by
  simp only [affineAverage, affineAverageAdjoint, map_mul, map_inv₀, map_natCast,
    map_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  calc
    _ = ∑ r : (ZMod p)ˣ, (p : ℂ)⁻¹ * conj (W r) *
        ∑ t : ZMod p, conj (F (affineGenerator r t)) * H t := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ r : (ZMod p)ˣ, (p : ℂ)⁻¹ * conj (W r) *
        ∑ t : ZMod p, conj (F t) * H (affineGeneratorInv r t) := by
      simp_rw [affineGenerator_inner_reindex]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro r _
      ring

theorem affineCoefficientSum_action {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) (t : ZMod p) :
    (∑ ab : (ZMod p)ˣ × ZMod p,
      affineCoefficientSum W ab * F ((ab.1 : ZMod p) * t + ab.2)) =
      ∑ r : (ZMod p)ˣ, ∑ s : (ZMod p)ˣ,
        conj (W r) * W s * F (affineGenerator s (affineGeneratorInv r t)) := by
  classical
  simp only [affineCoefficientSum, Finset.sum_mul, Finset.sum_filter, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rw [Fintype.sum_prod_type]
  simp_rw [← affineGenerator_comp_inv]

/-- The adjoint square is the affine action with the collected coefficient array. -/
theorem affineAverage_adjoint_square {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) :
    affineAverageAdjoint W (affineAverage W F) = affineAction (affineCoefficient W) F := by
  classical
  funext t
  calc
    _ = (p : ℂ)⁻¹ ^ 2 * ∑ r : (ZMod p)ˣ, ∑ s : (ZMod p)ˣ,
        conj (W r) * W s * F (affineGenerator s (affineGeneratorInv r t)) := by
      simp only [affineAverageAdjoint, affineAverage, Finset.mul_sum, pow_two]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = (p : ℂ)⁻¹ ^ 2 * ∑ ab : (ZMod p)ˣ × ZMod p,
        affineCoefficientSum W ab * F ((ab.1 : ZMod p) * t + ab.2) := by
      rw [affineCoefficientSum_action]
    _ = _ := by
      simp only [affineAction, affineCoefficient,
        Complex.ofReal_pow, Complex.ofReal_natCast, div_eq_mul_inv, inv_pow,
        Finset.mul_sum]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- Squared form of the mean-zero operator bound from Section 6. -/
theorem affineAverage_energy_sq_bound {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (hW : (∑ r : (ZMod p)ˣ, ‖W r‖ ^ 2) ≤ (p : ℝ))
    (F : ZMod p → ℂ) (hF : additiveFourier F 0 = 0) :
    (∑ t : ZMod p, ‖affineAverage W F t‖ ^ 2) ^ 2 ≤
      (3 / (p : ℝ)) * (∑ t : ZMod p, ‖F t‖ ^ 2) ^ 2 := by
  have hid : (∑ t : ZMod p, conj (affineAverage W F t) * affineAverage W F t) =
      ∑ t : ZMod p, conj (F t) * affineAction (affineCoefficient W) F t := by
    simpa only [affineAverage_adjoint_square] using
      affineAverage_adjoint_identity W F (affineAverage W F)
  have hcs := complex_sum_mul_sq Finset.univ (fun t : ZMod p => conj (F t))
    (affineAction (affineCoefficient W) F)
  rw [← hid] at hcs
  simp only [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_conj] at hcs
  have hnonneg : 0 ≤ ∑ t : ZMod p, ‖F t‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ (∑ t : ZMod p, ‖F t‖ ^ 2) *
        ∑ t : ZMod p, ‖affineAction (affineCoefficient W) F t‖ ^ 2 := hcs
    _ ≤ (∑ t : ZMod p, ‖F t‖ ^ 2) *
        ((3 / (p : ℝ)) * ∑ t : ZMod p, ‖F t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (affineAction_collected_energy_bound W hW F hF) hnonneg
    _ = _ := by ring

theorem affineAverage_energy_bound {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (hW : (∑ r : (ZMod p)ˣ, ‖W r‖ ^ 2) ≤ (p : ℝ))
    (F : ZMod p → ℂ) (hF : additiveFourier F 0 = 0) :
    (∑ t : ZMod p, ‖affineAverage W F t‖ ^ 2) ≤
      Real.sqrt (3 / (p : ℝ)) * ∑ t : ZMod p, ‖F t‖ ^ 2 := by
  have hR : 0 ≤ 3 / (p : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg p)
  have hE : 0 ≤ ∑ t : ZMod p, ‖F t‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) hE)).mp
  rw [mul_pow, Real.sq_sqrt hR]
  exact affineAverage_energy_sq_bound W hW F hF

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the constant Fourier mode

Centering a finite-field function removes exactly its zero frequency.
The energy splits into the centered energy and the squared mean.
-/

namespace Ostmann

open scoped BigOperators

theorem fieldCentered_fourier {p : ℕ} [NeZero p]
    (F : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fieldCentered F) a =
      additiveFourier F a - if a = 0 then fieldMean F else 0 := by
  unfold fieldCentered
  rw [additiveFourier_sub, additiveFourier_const]

theorem fieldCentered_fourier_zero {p : ℕ} [NeZero p] (F : ZMod p → ℂ) :
    additiveFourier (fieldCentered F) 0 = 0 := by
  simp only [fieldCentered_fourier, fieldMean, ite_true, if_true, sub_self]

theorem fieldCentered_energy_identity {p : ℕ} [NeZero p] (F : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖F x‖ ^ 2) =
      (∑ x : ZMod p, ‖fieldCentered F x‖ ^ 2) + (p : ℝ) * ‖fieldMean F‖ ^ 2 := by
  classical
  have hterm (a : ZMod p) : ‖additiveFourier F a‖ ^ 2 =
      ‖additiveFourier (fieldCentered F) a‖ ^ 2 +
        if a = 0 then ‖fieldMean F‖ ^ 2 else 0 := by
    by_cases ha : a = 0
    · subst a
      simp [fieldCentered_fourier_zero, fieldMean]
    · simp only [fieldCentered_fourier, ha, ite_false, if_false, sub_zero, add_zero]
  calc
    _ = (p : ℝ) * ∑ a : ZMod p, ‖additiveFourier F a‖ ^ 2 := additiveFourier_energy F
    _ = (p : ℝ) * ((∑ a : ZMod p, ‖additiveFourier (fieldCentered F) a‖ ^ 2) +
        ‖fieldMean F‖ ^ 2) := by
      simp_rw [hterm]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    _ = _ := by rw [additiveFourier_energy (fieldCentered F)]; ring

theorem fieldCentered_energy_le {p : ℕ} [NeZero p] (F : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖fieldCentered F x‖ ^ 2) ≤ ∑ x : ZMod p, ‖F x‖ ^ 2 := by
  rw [fieldCentered_energy_identity F]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg p) (sq_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Constant and mean-zero parts of the affine average

The self-correlation estimate here is the operator inequality used to
prove the uniform Mellin estimate in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem fieldMean_eq_sum {p : ℕ} [NeZero p] (F : ZMod p → ℂ) :
    fieldMean F = (p : ℂ)⁻¹ * ∑ t : ZMod p, F t := by
  rw [fieldMean, additiveFourier, ZMod.dft_apply_zero]

theorem affineAverage_mean {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) :
    fieldMean (affineAverage W F) = unitMean W * fieldMean F := by
  have hreindex (r : (ZMod p)ˣ) : (∑ t : ZMod p, F (affineGenerator r t)) =
      ∑ t : ZMod p, F t := (affineGeneratorEquiv r).bijective.sum_comp F
  rw [fieldMean_eq_sum, fieldMean_eq_sum]
  calc
    _ = (p : ℂ)⁻¹ ^ 2 * ∑ r : (ZMod p)ˣ,
        W r * ∑ t : ZMod p, F (affineGenerator r t) := by
      simp only [affineAverage, Finset.mul_sum, pow_two, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hreindex]
      rw [← Finset.sum_mul]
      unfold unitMean
      ring

theorem affineAverage_centered {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) (t : ZMod p) :
    affineAverage W (fieldCentered F) t =
      affineAverage W F t - unitMean W * fieldMean F := by
  simp only [affineAverage, fieldCentered, unitMean, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  ring

theorem affineAverage_centered_function {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) :
    affineAverage W (fieldCentered F) = fieldCentered (affineAverage W F) := by
  funext t
  rw [affineAverage_centered, fieldCentered, affineAverage_mean]

theorem affineAverage_full_energy_bound {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (hW : (∑ r : (ZMod p)ˣ, ‖W r‖ ^ 2) ≤ (p : ℝ))
    (F : ZMod p → ℂ) :
    (∑ t : ZMod p, ‖affineAverage W F t‖ ^ 2) ≤
      Real.sqrt (3 / (p : ℝ)) * (∑ t : ZMod p, ‖F t‖ ^ 2) +
        (p : ℝ) * ‖unitMean W‖ ^ 2 * ‖fieldMean F‖ ^ 2 := by
  rw [fieldCentered_energy_identity (affineAverage W F), affineAverage_mean,
    ← affineAverage_centered_function, norm_mul, mul_pow]
  have hcenter := (affineAverage_energy_bound W hW (fieldCentered F)
    (fieldCentered_fourier_zero F)).trans
      (mul_le_mul_of_nonneg_left (fieldCentered_energy_le F) (Real.sqrt_nonneg _))
  nlinarith

theorem unitMean_conj_of_zero {p : ℕ} [Fact p.Prime]
    (G : ZMod p → ℂ) (hG : G 0 = 0) :
    unitMean (fun r : (ZMod p)ˣ => conj (G r)) = conj (fieldMean G) := by
  unfold unitMean
  rw [sum_units_eq_sum_of_zero (fun x : ZMod p => conj (G x)) (by simp only [hG, map_zero]),
    fieldMean_eq_sum]
  simp only [map_mul, map_inv₀, map_natCast, map_sum]

/-- The exact affine self-correlation estimate underlying `src42`. -/
theorem affineAverage_self_correlation_bound {p : ℕ} [Fact p.Prime]
    (G : ZMod p → ℂ) (hG0 : G 0 = 0)
    (hG : (∑ t : ZMod p, ‖G t‖ ^ 2) ≤ (p : ℝ)) :
    (∑ t : ZMod p, ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2) /
      (p : ℝ) ≤ ‖fieldMean G‖ ^ 4 + Real.sqrt (3 / (p : ℝ)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hW : (∑ r : (ZMod p)ˣ, ‖conj (G r)‖ ^ 2) ≤ (p : ℝ) := by
    simp_rw [Complex.norm_conj]
    rw [sum_units_eq_sum_of_zero (fun t : ZMod p => ‖G t‖ ^ 2) (by simp [hG0])]
    exact hG
  have h := affineAverage_full_energy_bound (fun r : (ZMod p)ˣ => conj (G r)) hW G
  rw [unitMean_conj_of_zero G hG0, Complex.norm_conj] at h
  apply (div_le_iff₀ hp).mpr
  have hs := mul_le_mul_of_nonneg_left hG (Real.sqrt_nonneg (3 / (p : ℝ)))
  nlinarith

/-- Restricting the output to units costs only the factor `p/(p-1)`. -/
theorem affineAverage_self_correlation_unit_bound {p : ℕ} [Fact p.Prime]
    (G : ZMod p → ℂ) (hG0 : G 0 = 0)
    (hG : (∑ t : ZMod p, ‖G t‖ ^ 2) ≤ (p : ℝ)) :
    (∑ t : (ZMod p)ˣ, ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2) /
      ((p : ℝ) - 1) ≤ ((p : ℝ) / ((p : ℝ) - 1)) *
        (‖fieldMean G‖ ^ 4 + Real.sqrt (3 / (p : ℝ))) := by
  classical
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : 0 < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  have hsub : (∑ t : (ZMod p)ˣ,
      ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2) ≤
      ∑ t : ZMod p, ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2 :=
    OAI.sum_le_sum_of_injOn (fun t : (ZMod p)ˣ => (t : ZMod p))
      Units.val_injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
      (fun _ _ _ => sq_nonneg _)
  calc
    _ ≤ (∑ t : ZMod p, ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2) /
        ((p : ℝ) - 1) := div_le_div_of_nonneg_right hsub hp1.le
    _ = ((p : ℝ) / ((p : ℝ) - 1)) *
        ((∑ t : ZMod p, ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2) /
          (p : ℝ)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (affineAverage_self_correlation_bound G hG0 hG) (div_nonneg hp.le hp1.le)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_Mellin
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem mellin_orthogonality {p : ℕ} [Fact p.Prime]
    (χ ρ : MulChar (ZMod p) ℂ) :
    (∑ z : (ZMod p)ˣ, χ z * conj (ρ z)) =
      if χ = ρ then (Fintype.card (ZMod p)ˣ : ℂ) else 0 := by
  have hterm : ∀ z : (ZMod p)ˣ, χ z * conj (ρ z) = (χ * ρ⁻¹) z := by
    intro z
    rw [MulChar.coeToFun_mul, Pi.mul_apply, MulChar.inv_apply_eq_inv',
      Complex.inv_eq_conj (norm_mulChar_unit ρ z)]
  simp_rw [hterm]
  rw [sum_mulChar_units_eq_ite]
  simp only [mul_inv_eq_one]

/-- Character orthogonality computes the square-pullback coefficient. -/
theorem mellinCoefficient_square_pullback {p : ℕ} [Fact p.Prime]
    (s : Finset (MulChar (ZMod p) ℂ)) (c : MulChar (ZMod p) ℂ → ℂ)
    (f : (ZMod p)ˣ → ℂ) (hf : ∀ z, f z = ∑ χ ∈ s, c χ * χ z)
    (K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    mellinCoefficient (fun z => f (K * z ^ 2)) ρ =
      ∑ χ ∈ s.filter (fun χ => χ ^ 2 = ρ), c χ * χ K := by
  classical
  have hcard : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold mellinCoefficient
  simp_rw [hf, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  calc
    _ = ∑ χ ∈ s, (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ *
        (c χ * χ K * ∑ z : (ZMod p)ˣ, (χ ^ 2) z * conj (ρ z)) := by
      apply Finset.sum_congr rfl
      intro χ _
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
        MulChar.pow_apply_coe]
      ring
    _ = _ := by
      simp_rw [mellin_orthogonality]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro χ _
      by_cases hχ : χ ^ 2 = ρ
      · simp only [hχ, ite_true, if_true]
        field_simp
      · simp only [hχ, ite_false, if_false, mul_zero]

/-- Equation `tree-square-pullback` for a finite Mellin expansion. -/
theorem mellinCoefficient_square_pullback_bound {p : ℕ} [Fact p.Prime]
    (s : Finset (MulChar (ZMod p) ℂ)) (c : MulChar (ZMod p) ℂ → ℂ)
    (f : (ZMod p)ˣ → ℂ) (hf : ∀ z, f z = ∑ χ ∈ s, c χ * χ z)
    (K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun z => f (K * z ^ 2)) ρ‖ ^ 2 ≤
      2 * ∑ χ ∈ s.filter (fun χ => χ ^ 2 = ρ), ‖c χ‖ ^ 2 := by
  rw [mellinCoefficient_square_pullback s c f hf K ρ]
  exact square_pullback_coefficients s c K ρ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MellinParseval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
noncomputable local instance instDecidableEqMulCharZModComplex_solutions_2_rfc8d08_1 {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) :=
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
-- module Solutions.OAIQ095_OS.Ostmann_Tree_BottomPairCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinates for a bottom pair of the finite-field tree

The change of variables in §6 sends `(d,t)` to `(dt/(t-1),d/(t-1))`.
On its valid domain this is a bijection with the ordered distinct nonzero
pairs. It is the change of variables used in the bottom-pair second moment.
-/

namespace Ostmann

variable {K : Type*} [Field K]

theorem pair_coordinate_difference (d t : K) (ht : t ≠ 1) :
    d * t / (t - 1) - d / (t - 1) = d := by
  have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  field_simp

theorem pair_coordinates_reconstruct (x z : K) (hz : z ≠ 0) (hxz : x ≠ z) :
    ((x - z) * (x / z) / (x / z - 1), (x - z) / (x / z - 1)) = (x, z) := by
  have hden : x / z - 1 ≠ 0 := by
    intro h
    have : x / z = 1 := sub_eq_zero.mp h
    exact hxz ((div_eq_one_iff_eq hz).mp this)
  have hsub : x - z ≠ 0 := sub_ne_zero.mpr hxz
  apply Prod.ext <;> dsimp
  · field_simp [hsub]
  · field_simp [hsub]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BottomPairMellin
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The bottom-pair Mellin coefficient is an autocorrelation

This is equation `tree-P-definition`. The difference parameter is a unit;
the exceptional ratio `t = 1` is assigned value zero. The function being
correlated is twisted by the conjugate multiplicative character.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private theorem sum_units_of_zero {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (hF : F 0 = 0) :
    (∑ u : (ZMod p)ˣ, F u) = ∑ x : ZMod p, F x := by
  classical
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun x : ZMod p => x ≠ 0) F
  have hz : (∑ x : {x : ZMod p // ¬x ≠ 0}, F x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hx : x.val = 0 := not_ne_iff.mp x.property
    simpa only [hx] using hF
  rw [hz, add_zero] at hsum
  calc
    (∑ u : (ZMod p)ˣ, F u) = ∑ x : {x : ZMod p // x ≠ 0}, F x :=
      (unitsEquivNeZero (G₀ := ZMod p)).bijective.sum_comp (fun x => F x.val)
    _ = _ := hsum

theorem ratioInvolution_involutive {p : ℕ} [Fact p.Prime] :
    Function.Involutive (ratioInvolution (p := p)) := by
  intro t
  by_cases ht : t = 1
  · simp [ratioInvolution, ht]
  · have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht
    have hquot : t / (t - 1) ≠ 1 := by
      intro h
      have heq := (div_eq_one_iff_eq hden).mp h
      have : (1 : ZMod p) = 0 := by linear_combination heq
      exact one_ne_zero this
    simp only [ratioInvolution, ht, ite_false, if_false, hquot]
    field_simp
    ring

private theorem twisted_pair_identity {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (d : (ZMod p)ˣ) (t : ZMod p) (ht : t ≠ 1) :
    characterTwist g χ ((d : ZMod p) * t / (t - 1)) *
        conj (characterTwist g χ ((d : ZMod p) * t / (t - 1) - d)) =
      g ((d : ZMod p) * t / (t - 1)) * conj (g ((d : ZMod p) / (t - 1))) *
        conj (χ t) := by
  let x : ZMod p := (d : ZMod p) * t / (t - 1)
  let z : ZMod p := (d : ZMod p) / (t - 1)
  have hz : z ≠ 0 := div_ne_zero (Units.ne_zero d) (sub_ne_zero.mpr ht)
  have hdiff : x - d = z := by
    dsimp [x, z]
    have hh := pair_coordinate_difference (d : ZMod p) t ht
    linear_combination hh
  have hx : x = t * z := by dsimp [x, z]; ring
  have hchar : χ x = χ t * χ z := by rw [hx, map_mul]
  have hnorm : ‖χ z‖ = 1 := norm_mulChar_unit χ (Units.mk0 z hz)
  change (g x * conj (χ x)) * conj (g (x - d) * conj (χ (x - d))) =
    g x * conj (g z) * conj (χ t)
  rw [hdiff]
  calc
    _ = (g x * conj (g z) * conj (χ t)) * (conj (χ z) * χ z) := by
      rw [hchar]
      simp only [map_mul, starRingEnd_apply, star_star]
      ring
    _ = _ := by rw [Complex.conj_mul', hnorm]; norm_num

/-- Reindex the unnormalized bottom-pair Mellin sum as a full-field correlation. -/
theorem bottomPair_mellin_sum {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : (ZMod p)ˣ) (χ : MulChar (ZMod p) ℂ) :
    (∑ t : (ZMod p)ˣ, bottomPairValue g d t * conj (χ t)) =
      ∑ x : ZMod p, characterTwist g χ x * conj (characterTwist g χ (x - d)) := by
  classical
  let H : ZMod p → ℂ := fun t => if t = 1 then 0 else
    g ((d : ZMod p) * t / (t - 1)) *
      conj (g ((d : ZMod p) / (t - 1))) * conj (χ t)
  have hH0 : H 0 = 0 := by simp [H, MulChar.map_zero]
  have hunit : ∀ t : (ZMod p)ˣ, bottomPairValue g d t * conj (χ t) = H t := by
    intro t
    by_cases ht : t = 1
    · subst t
      simp [bottomPairValue, H]
    · have htval : (t : ZMod p) ≠ 1 := fun h => ht (Units.ext h)
      simp only [bottomPairValue, ht, ite_false, if_false, H, htval]
  let e : ZMod p ≃ ZMod p :=
    (Function.Involutive.toPerm _ ratioInvolution_involutive).trans
      (Equiv.mulLeft₀ (d : ZMod p) (Units.ne_zero d))
  have he : ∀ t : ZMod p, H t =
      characterTwist g χ (e t) * conj (characterTwist g χ (e t - d)) := by
    intro t
    change H t = characterTwist g χ ((d : ZMod p) * ratioInvolution t) *
      conj (characterTwist g χ ((d : ZMod p) * ratioInvolution t - d))
    by_cases ht : t = 1
    · subst t
      simp [H, ratioInvolution, characterTwist, MulChar.map_zero]
    · simpa only [H, ht, ite_false, if_false, ratioInvolution, ← mul_div_assoc] using
        (twisted_pair_identity g χ d t ht).symm
  simp_rw [hunit]
  rw [sum_units_of_zero H hH0]
  simp_rw [he]
  exact e.bijective.sum_comp (fun x => characterTwist g χ x * conj (characterTwist g χ (x - d)))

/-- Equation `tree-P-definition`, with the paper's two probability normalizations. -/
theorem bottomPair_mellin_autocorrelation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : (ZMod p)ˣ) (χ : MulChar (ZMod p) ℂ) :
    mellinCoefficient (bottomPairValue g d) χ =
      (p : ℂ) / (Fintype.card (ZMod p)ˣ : ℂ) *
        additiveAutocorrelation (characterTwist g χ) (d : ZMod p) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mellinCoefficient, bottomPair_mellin_sum, additiveAutocorrelation]
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_GaussFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem gaussSum_norm_sq {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2 = (p : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ (ZMod.isPrimitive_stdAddChar p)
  rw [← star_gaussSum_eq] at h
  change gaussSum χ ZMod.stdAddChar * conj (gaussSum χ ZMod.stdAddChar) = _ at h
  rw [Complex.mul_conj', ZMod.card] at h
  exact_mod_cast h

theorem additiveFourier_mulChar_unit {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (a : (ZMod p)ˣ) :
    additiveFourier χ (a : ZMod p) =
      (p : ℂ)⁻¹ * χ⁻¹ (-(a : ZMod p)) * gaussSum χ (ZMod.stdAddChar (N := p)) := by
  rw [additiveFourier_apply]
  have hsum : (∑ x : ZMod p, χ x * ZMod.stdAddChar (-(x * (a : ZMod p)))) =
      gaussSum χ ((ZMod.stdAddChar (N := p)).mulShift (-a)) := by
    simp only [gaussSum, AddChar.mulShift_apply]
    congr 1
    funext x
    rw [neg_mul, mul_comm (a : ZMod p) x]
  have hshift := gaussSum_mulShift_eq χ (ZMod.stdAddChar (N := p)) (-a)
  simp only [Units.val_neg] at hshift
  rw [hsum, hshift]
  ring

/-- A nonprincipal character has zero additive Fourier coefficient at zero. -/
theorem additiveFourier_mulChar_zero {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) : additiveFourier χ 0 = 0 := by
  simp [additiveFourier_apply, χ.sum_eq_zero_of_ne_one hχ]

theorem additiveFourier_mulChar {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    additiveFourier χ a =
      (p : ℂ)⁻¹ * χ⁻¹ (-a) * gaussSum χ (ZMod.stdAddChar (N := p)) := by
  by_cases ha : a = 0
  · subst a
    simp only [additiveFourier_mulChar_zero χ hχ, neg_zero, MulChar.map_zero, mul_zero,
      zero_mul]
  · exact additiveFourier_mulChar_unit χ (Units.mk0 a ha)

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

/-- Exact Gauss convolution formula, including the vanishing zero term. -/
theorem additiveFourier_mul_character {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    additiveFourier (fun x => f x * χ x) a =
      ((p : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := p))) *
        ∑ b : ZMod p, additiveFourier f b * χ⁻¹ (-(a - b)) := by
  rw [additiveFourier_pointwise_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [additiveFourier_mulChar χ hχ]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy and the principal-character correction

All characters, including the principal one, vanish at zero. Multiplying
by a character cannot increase Fourier energy, and the principal twist
subtracts the zero-point contribution from every Fourier coefficient.
-/

namespace Ostmann

open scoped BigOperators

theorem norm_mulChar_le_one {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (x : ZMod p) : ‖χ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · exact (norm_mulChar_unit χ (Units.mk0 x hx)).le

theorem additiveFourier_character_energy_le {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) :
    (∑ a : ZMod p, ‖additiveFourier (fun x => f x * χ x) a‖ ^ 2) ≤
      ∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2 := by
  rw [additiveFourier_parseval, additiveFourier_parseval]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg p))
  apply Finset.sum_le_sum
  intro x _
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_mulChar_le_one χ x)

theorem additiveFourier_principal_twist {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => f x * (1 : MulChar (ZMod p) ℂ) x) a =
      additiveFourier f a - (p : ℂ)⁻¹ * f 0 := by
  classical
  have hpoint : (fun x => f x * (1 : MulChar (ZMod p) ℂ) x) =
      (fun x => f x - if x = 0 then f 0 else 0) := by
    funext x
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · simp only [hx, ite_false, if_false, sub_zero]
      rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx), mul_one]
  rw [hpoint, additiveFourier_sub]
  congr 1
  simp [additiveFourier_apply]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPairCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coincidences between two monic split quadratics

Distinct unordered pairs give monic quadratics whose equality can hold at
at most one point. This is the counting step in the fourth-moment estimate.
-/

namespace Ostmann

/-- Equality at two distinct points forces equality of the unordered roots. -/
theorem quadraticPair_eq_of_two_points {K : Type*} [Field K]
    (b₁ b₂ b₃ b₄ a a' : K) (haa : a ≠ a')
    (ha : (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))
    (ha' : (a' - b₁) * (a' - b₂) = (a' - b₃) * (a' - b₄)) :
    (b₁ = b₃ ∧ b₂ = b₄) ∨ (b₁ = b₄ ∧ b₂ = b₃) := by
  have hlin : (a - a') * (b₁ + b₂ - b₃ - b₄) = 0 := by
    linear_combination -ha + ha'
  have hsum : b₁ + b₂ = b₃ + b₄ := by
    have hzero := (mul_eq_zero.mp hlin).resolve_left (sub_ne_zero.mpr haa)
    linear_combination hzero
  have hprod : b₁ * b₂ = b₃ * b₄ := by
    linear_combination ha + a * hsum
  have hroot : (b₁ - b₃) * (b₁ - b₄) = 0 := by
    linear_combination b₁ * hsum - hprod
  rcases mul_eq_zero.mp hroot with h | h
  · left
    have h₁₃ : b₁ = b₃ := sub_eq_zero.mp h
    refine ⟨h₁₃, ?_⟩
    linear_combination hsum - h₁₃
  · right
    have h₁₄ : b₁ = b₄ := sub_eq_zero.mp h
    refine ⟨h₁₄, ?_⟩
    linear_combination hsum - h₁₄

/-- Off the two diagonals, there is at most one coincidence. -/
theorem quadraticPair_collision_card_le_one {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (b₁ b₂ b₃ b₄ : K)
    (hdiag : ¬ ((b₁ = b₃ ∧ b₂ = b₄) ∨ (b₁ = b₄ ∧ b₂ = b₃))) :
    (Finset.univ.filter (fun a : K =>
      (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha a' ha'
  by_contra hne
  exact hdiag (quadraticPair_eq_of_two_points b₁ b₂ b₃ b₄ a a' hne
    (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp ha').2)

/-- The two diagonal pairings account for every exceptional collision fiber. -/
theorem quadraticPair_collision_count_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (b₁ b₂ b₃ b₄ : K) :
    ((Finset.univ.filter (fun a : K =>
      (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card : ℝ) ≤
      1 + (Fintype.card K : ℝ) *
        ((if b₁ = b₃ ∧ b₂ = b₄ then 1 else 0) +
          (if b₁ = b₄ ∧ b₂ = b₃ then 1 else 0)) := by
  have hcard : ((Finset.univ.filter (fun a : K =>
      (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card : ℝ) ≤ Fintype.card K := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset
      (fun a : K => (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄)) Finset.univ)
  have hp : (0 : ℝ) ≤ Fintype.card K := Nat.cast_nonneg _
  by_cases h₁ : b₁ = b₃ ∧ b₂ = b₄
  · by_cases h₂ : b₁ = b₄ ∧ b₂ = b₃
    · rw [ite_eq_left h₁, ite_eq_left h₂]
      linarith
    · rw [ite_eq_left h₁, ite_eq_right h₂]
      linarith
  · by_cases h₂ : b₁ = b₄ ∧ b₂ = b₃
    · rw [ite_eq_right h₁, ite_eq_left h₂]
      linarith
    · rw [ite_eq_right h₁, ite_eq_right h₂]
      simp only [add_zero, mul_zero]
      exact_mod_cast quadraticPair_collision_card_le_one b₁ b₂ b₃ b₄
        (not_or.mpr ⟨h₁, h₂⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_WeightedQuadraticCollisions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted coincidences of split quadratics

The two diagonal pairings contribute the squared second moment; every
other quadruple has at most one collision. This proves the counting
inequality underlying the character fourth moment in Section 6.
-/

namespace Ostmann

open scoped BigOperators

private theorem sum_four_weights {K : Type*} [Fintype K] (w : K → ℝ) :
    (∑ b₁ : K, ∑ b₂ : K, ∑ b₃ : K, ∑ b₄ : K,
      w b₁ * w b₂ * w b₃ * w b₄) = (∑ b : K, w b) ^ 4 := by
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private theorem sum_paired_weights {K : Type*} [Fintype K] [DecidableEq K]
    (w : K → ℝ) :
    (∑ b₁ : K, ∑ b₂ : K, ∑ b₃ : K, ∑ b₄ : K,
      w b₁ * w b₂ * w b₃ * w b₄ *
        (if b₁ = b₃ ∧ b₂ = b₄ then 1 else 0)) = (∑ b : K, w b ^ 2) ^ 2 := by
  simp only [mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, Finset.sum_const_zero]
  calc
    _ = ∑ b₁ : K, ∑ b₂ : K, w b₁ ^ 2 * w b₂ ^ 2 := by
      apply Finset.sum_congr rfl
      intro b₁ _
      apply Finset.sum_congr rfl
      intro b₂ _
      ring
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

private theorem sum_crossed_weights {K : Type*} [Fintype K] [DecidableEq K]
    (w : K → ℝ) :
    (∑ b₁ : K, ∑ b₂ : K, ∑ b₃ : K, ∑ b₄ : K,
      w b₁ * w b₂ * w b₃ * w b₄ *
        (if b₁ = b₄ ∧ b₂ = b₃ then 1 else 0)) = (∑ b : K, w b ^ 2) ^ 2 := by
  simp only [mul_ite, mul_one, mul_zero, ite_and,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  calc
    _ = ∑ b₁ : K, ∑ b₂ : K, w b₁ ^ 2 * w b₂ ^ 2 := by
      apply Finset.sum_congr rfl
      intro b₁ _
      apply Finset.sum_congr rfl
      intro b₂ _
      ring
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

/-- The weighted collision count is at most `2 |K| r² + J⁴`. -/
theorem weighted_quadratic_collisions_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (w : K → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ b₁ : K, ∑ b₂ : K, ∑ b₃ : K, ∑ b₄ : K,
      w b₁ * w b₂ * w b₃ * w b₄ *
        ((Finset.univ.filter (fun a : K =>
          (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card : ℝ)) ≤
      2 * (Fintype.card K : ℝ) * (∑ b : K, w b ^ 2) ^ 2 + (∑ b : K, w b) ^ 4 := by
  calc
    _ ≤ ∑ b₁ : K, ∑ b₂ : K, ∑ b₃ : K, ∑ b₄ : K,
        w b₁ * w b₂ * w b₃ * w b₄ *
          (1 + (Fintype.card K : ℝ) *
            ((if b₁ = b₃ ∧ b₂ = b₄ then 1 else 0) +
              (if b₁ = b₄ ∧ b₂ = b₃ then 1 else 0))) := by
      refine Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ =>
        Finset.sum_le_sum fun b₃ _ => Finset.sum_le_sum fun b₄ _ => ?_
      exact mul_le_mul_of_nonneg_left (quadraticPair_collision_count_le b₁ b₂ b₃ b₄)
        (mul_nonneg (mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _)) (hw _))
    _ = _ := by
      simp_rw [mul_add, mul_one]
      simp only [Finset.sum_add_distrib]
      have hpair := sum_paired_weights w
      have hcross := sum_crossed_weights w
      have hmass := sum_four_weights w
      simp_rw [← mul_assoc, mul_right_comm _ (Fintype.card K : ℝ)]
      simp only [← Finset.sum_mul]
      rw [hmass, hpair, hcross]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFourthMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A weighted fourth moment of multiplicative character sums

The full character sum selects equality of two nonzero products. Together
with the split-quadratic collision count, this gives equation
`tree-fourth-moment` of the manuscript.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.characterFourthFintype
theorem mellin_field_dual_orthogonality {p : ℕ} [Fact p.Prime]
    (x z : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ, χ x * conj (χ z)) =
      if x = z ∧ x ≠ 0 then (Fintype.card (ZMod p)ˣ : ℂ) else 0 := by
  classical
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  by_cases hz : z = 0
  · simp [hz, MulChar.map_zero]
  have h := mellin_dual_orthogonality (Units.mk0 x hx) (Units.mk0 z hz)
  have heq : (x = z ∧ x ≠ 0) ↔ x = z := and_iff_left hx
  simpa only [Units.val_mk0, Units.mk0_inj, heq] using h

theorem weightedCharacterSum_fourth_expansion {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    ((‖weightedCharacterSum w χ a‖ ^ 4 : ℝ) : ℂ) =
      ∑ b₁ : ZMod p, ∑ b₂ : ZMod p, ∑ b₃ : ZMod p, ∑ b₄ : ZMod p,
        ((w b₁ * w b₂ * w b₃ * w b₄ : ℝ) : ℂ) *
          χ ((a - b₁) * (a - b₂)) * conj (χ ((a - b₃) * (a - b₄))) := by
  have hconj : conj (weightedCharacterSum w χ a) =
      ∑ b : ZMod p, (w b : ℂ) * conj (χ (a - b)) := by
    simp [weightedCharacterSum, map_sum, map_mul]
  calc
    _ = (weightedCharacterSum w χ a * conj (weightedCharacterSum w χ a)) ^ 2 := by
      rw [Complex.mul_conj']
      push_cast
      ring
    _ = (∑ b₁ : ZMod p, (w b₁ : ℂ) * conj (χ (a - b₁))) *
        (∑ b₂ : ZMod p, (w b₂ : ℂ) * conj (χ (a - b₂))) *
        (∑ b₃ : ZMod p, (w b₃ : ℂ) * χ (a - b₃)) *
        (∑ b₄ : ZMod p, (w b₄ : ℂ) * χ (a - b₄)) := by
      rw [hconj]
      unfold weightedCharacterSum
      ring
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b₁ _
      apply Finset.sum_congr rfl
      intro b₂ _
      apply Finset.sum_congr rfl
      intro b₃ _
      apply Finset.sum_congr rfl
      intro b₄ _
      simp only [map_mul, Complex.ofReal_mul]
      ring

/-- Character orthogonality leaves exactly the nonzero product collisions. -/
theorem weightedCharacterSum_fourth_character_sum {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (a : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ, ‖weightedCharacterSum w χ a‖ ^ 4) =
      (Fintype.card (ZMod p)ˣ : ℝ) *
        ∑ b₁ : ZMod p, ∑ b₂ : ZMod p, ∑ b₃ : ZMod p, ∑ b₄ : ZMod p,
          if (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄) ∧
              (a - b₁) * (a - b₂) ≠ 0 then w b₁ * w b₂ * w b₃ * w b₄ else 0 := by
  classical
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  simp_rw [weightedCharacterSum_fourth_expansion]
  calc
    _ = ∑ b₁ : ZMod p, ∑ b₂ : ZMod p, ∑ b₃ : ZMod p, ∑ b₄ : ZMod p,
        ((w b₁ * w b₂ * w b₃ * w b₄ : ℝ) : ℂ) *
          ∑ χ : MulChar (ZMod p) ℂ,
            χ ((a - b₁) * (a - b₂)) * conj (χ ((a - b₃) * (a - b₄))) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b₁ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b₂ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b₃ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b₄ _
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by
      simp_rw [mellin_field_dual_orthogonality]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b₁ _
      apply Finset.sum_congr rfl
      intro b₂ _
      apply Finset.sum_congr rfl
      intro b₃ _
      apply Finset.sum_congr rfl
      intro b₄ _
      split_ifs <;> push_cast <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFourthBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The weighted character fourth-moment bound

Equation `tree-fourth-moment` follows from character orthogonality and
counting coincidences of two monic split quadratics.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.characterFourthBoundFintype
/-- The fourth-moment bound, with the manuscript's normalization. -/
theorem weightedCharacterSum_fourth_bound {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖weightedCharacterSum w χ a‖ ^ 4) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤
        2 * (p : ℝ) * (∑ b : ZMod p, w b ^ 2) ^ 2 + (∑ b : ZMod p, w b) ^ 4 := by
  classical
  let W : ZMod p → ZMod p → ZMod p → ZMod p → ℝ :=
    fun b₁ b₂ b₃ b₄ => w b₁ * w b₂ * w b₃ * w b₄
  let V : ZMod p → ZMod p → ZMod p → ZMod p → ZMod p → ℝ :=
    fun a b₁ b₂ b₃ b₄ =>
      if (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄) ∧
          (a - b₁) * (a - b₂) ≠ 0 then W b₁ b₂ b₃ b₄ else 0
  have hW (b₁ b₂ b₃ b₄ : ZMod p) : 0 ≤ W b₁ b₂ b₃ b₄ :=
    mul_nonneg (mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _)) (hw _)
  have hswap : (∑ a : ZMod p, ∑ b₁ : ZMod p, ∑ b₂ : ZMod p,
      ∑ b₃ : ZMod p, ∑ b₄ : ZMod p, V a b₁ b₂ b₃ b₄) =
      ∑ b₁ : ZMod p, ∑ b₂ : ZMod p, ∑ b₃ : ZMod p,
        ∑ b₄ : ZMod p, ∑ a : ZMod p, V a b₁ b₂ b₃ b₄ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b₁ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b₂ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b₃ _
    rw [Finset.sum_comm]
  have hlocal (b₁ b₂ b₃ b₄ : ZMod p) : (∑ a : ZMod p, V a b₁ b₂ b₃ b₄) ≤
      W b₁ b₂ b₃ b₄ *
        ((Finset.univ.filter (fun a : ZMod p =>
          (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card : ℝ) := by
    calc
      _ ≤ ∑ a : ZMod p,
          if (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄) then W b₁ b₂ b₃ b₄ else 0 := by
        apply Finset.sum_le_sum
        intro a _
        dsimp only [V]
        by_cases he : (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄)
        · rw [ite_eq_left he]
          by_cases hn : (a - b₁) * (a - b₂) ≠ 0
          · rw [ite_eq_left ⟨he, hn⟩]
          · rw [ite_eq_right (fun h => hn h.2)]
            exact hW b₁ b₂ b₃ b₄
        · rw [ite_eq_right he, ite_eq_right (fun h => he h.1)]
      _ = _ := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hsum : (∑ a : ZMod p, ∑ b₁ : ZMod p, ∑ b₂ : ZMod p,
      ∑ b₃ : ZMod p, ∑ b₄ : ZMod p, V a b₁ b₂ b₃ b₄) ≤
      2 * (p : ℝ) * (∑ b : ZMod p, w b ^ 2) ^ 2 + (∑ b : ZMod p, w b) ^ 4 := by
    rw [hswap]
    calc
      _ ≤ ∑ b₁ : ZMod p, ∑ b₂ : ZMod p, ∑ b₃ : ZMod p, ∑ b₄ : ZMod p,
          W b₁ b₂ b₃ b₄ *
            ((Finset.univ.filter (fun a : ZMod p =>
              (a - b₁) * (a - b₂) = (a - b₃) * (a - b₄))).card : ℝ) := by
        exact Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ =>
          Finset.sum_le_sum fun b₃ _ => Finset.sum_le_sum fun b₄ _ => hlocal b₁ b₂ b₃ b₄
      _ ≤ _ := by simpa only [W, ZMod.card] using weighted_quadratic_collisions_le w hw
  have hcard : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  rw [Finset.sum_comm]
  simp_rw [weightedCharacterSum_fourth_character_sum]
  rw [← Finset.mul_sum]
  simpa only [V, W, mul_comm] using mul_le_mul_of_nonneg_left hsum hcard.le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquareAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Domination of a uniform square-coset average

The square map on the unit group has fibers of size at most two. Its
pushforward therefore has density at most two against the uniform law.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_square_coset_le_twice {p : ℕ} [Fact p.Prime]
    (K : (ZMod p)ˣ) (f : (ZMod p)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u) :
    (∑ z : (ZMod p)ˣ, f (K * z ^ 2)) ≤ 2 * ∑ u : (ZMod p)ˣ, f u := by
  classical
  have hmaps : ∀ z ∈ (Finset.univ : Finset (ZMod p)ˣ),
      K * z ^ 2 ∈ (Finset.univ : Finset (ZMod p)ˣ) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun z => f (K * z ^ 2)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  have heq : (Finset.univ.filter (fun z : (ZMod p)ˣ => K * z ^ 2 = u)) =
      Finset.univ.filter (fun z : (ZMod p)ˣ => z ^ 2 = K⁻¹ * u) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]
    · intro h
      rw [h, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsum : (∑ z ∈ Finset.univ.filter (fun z : (ZMod p)ˣ => K * z ^ 2 = u),
      f (K * z ^ 2)) =
      ((Finset.univ.filter (fun z : (ZMod p)ˣ => z ^ 2 = K⁻¹ * u)).card : ℝ) * f u := by
    calc
      _ = ∑ _z ∈ Finset.univ.filter (fun z : (ZMod p)ˣ => K * z ^ 2 = u), f u := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [(Finset.mem_filter.mp hz).2]
      _ = _ := by simp only [heq, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  apply mul_le_mul_of_nonneg_right _ (hf u)
  exact_mod_cast unit_square_fiber_card_le_two Finset.univ (K⁻¹ * u)

/-- Inverting the sampling coordinate preserves the same square-coset bound. -/
theorem sum_inverse_square_coset_le_twice {p : ℕ} [Fact p.Prime]
    (K : (ZMod p)ˣ) (f : (ZMod p)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u) :
    (∑ z : (ZMod p)ˣ, f (K * (z⁻¹) ^ 2)) ≤ 2 * ∑ u : (ZMod p)ˣ, f u := by
  have h := (Equiv.inv (ZMod p)ˣ).bijective.sum_comp
    (fun z => f (K * z ^ 2))
  change (∑ z : (ZMod p)ˣ, f (K * (z⁻¹) ^ 2)) = _ at h
  rw [h]
  exact sum_square_coset_le_twice K f hf

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalFourthMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the principal character from the fourth moment

Its contribution cancels the leading fourth power of the total mass.
This leaves the second-moment term required by the two-bad quartet case.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.principalFourthDecidableEq
theorem weightedCharacterSum_principal {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (a : ZMod p) :
    weightedCharacterSum w 1 a = ((∑ b : ZMod p, w b) - w a : ℝ) := by
  classical
  have hterm (b : ZMod p) : (w b : ℂ) * (1 : MulChar (ZMod p) ℂ) (a - b) =
      (w b : ℂ) - if b = a then (w a : ℂ) else 0 := by
    by_cases hb : b = a
    · simp [hb, MulChar.map_zero]
    · have hab : a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
      rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hab)]
      simp only [hb, ite_false, if_false, sub_zero, mul_one]
  simp only [weightedCharacterSum, hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, Complex.ofReal_sub, Complex.ofReal_sum]

private theorem fourth_tangent (J x : ℝ) : J ^ 4 - 4 * J ^ 3 * x ≤ (J - x) ^ 4 := by
  have h : 0 ≤ x ^ 2 * ((x - 2 * J) ^ 2 + 2 * J ^ 2) := by positivity
  nlinarith

theorem principal_fourth_moment_lower {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) :
    ((p : ℝ) - 4) * (∑ b : ZMod p, w b) ^ 4 ≤
      ∑ a : ZMod p, ‖weightedCharacterSum w 1 a‖ ^ 4 := by
  simp_rw [weightedCharacterSum_principal, Complex.norm_real, Real.norm_eq_abs,
    (show Even (4 : ℕ) by decide).pow_abs]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (a : ZMod p) _ => fourth_tangent (∑ b : ZMod p, w b) (w a))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, ← Finset.mul_sum] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

attribute [local instance] OAI.Ostmann.principalFourthFintype
/-- The leading `J⁴` cancels after removing the principal character. -/
theorem nonprincipal_fourth_moment_bound {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ χ ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
      ∑ a : ZMod p, ‖weightedCharacterSum w χ a‖ ^ 4) ≤
      2 * (p : ℝ) * (Fintype.card (ZMod p)ˣ : ℝ) *
        (∑ b : ZMod p, w b ^ 2) ^ 2 + 3 * (∑ b : ZMod p, w b) ^ 4 := by
  classical
  have hc : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  have htotal := (div_le_iff₀ hc).mp (weightedCharacterSum_fourth_bound w hw)
  have hprincipal := principal_fourth_moment_lower w
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (MulChar (ZMod p) ℂ))
    (fun χ => ∑ a : ZMod p, ‖weightedCharacterSum w χ a‖ ^ 4) (Finset.mem_univ 1)
  rw [hcard] at htotal ⊢
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_GaussFourthMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourth moments after a nonprincipal multiplicative twist

Gauss convolution transfers the weighted character fourth moment to
Fourier coefficients. The character inversion merely permutes the
nonprincipal characters.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.gaussFourthDecidableEq
theorem normalizedGauss_norm_sq {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ‖(p : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2 = (p : ℝ)⁻¹ := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast, gaussSum_norm_sq χ hχ]
  field_simp

theorem additiveFourier_character_norm_four {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ b, additiveFourier f b = (w b : ℂ))
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    ‖additiveFourier (fun x => f x * χ x) a‖ ^ 4 =
      ((p : ℝ)⁻¹) ^ 2 * ‖weightedCharacterSum w χ⁻¹ a‖ ^ 4 := by
  have hphase (b : ZMod p) : χ⁻¹ (-(a - b)) = χ⁻¹ (-1) * χ⁻¹ (a - b) := by
    rw [← map_mul]
    congr 1
    ring
  have hsum : (∑ b : ZMod p, additiveFourier f b * χ⁻¹ (-(a - b))) =
      χ⁻¹ (-1) * weightedCharacterSum w χ⁻¹ a := by
    simp only [hf, weightedCharacterSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [hphase]
    ring
  rw [additiveFourier_mul_character f χ hχ, hsum, norm_mul,
    norm_mul (χ⁻¹ (-1)) (weightedCharacterSum w χ⁻¹ a),
    show ‖χ⁻¹ (-1)‖ = 1 from norm_mulChar_unit χ⁻¹ (-1), one_mul, mul_pow]
  have hfour : ‖(p : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 4 =
      ((p : ℝ)⁻¹) ^ 2 := by
    calc
      _ = (‖(p : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2) ^ 2 := by ring
      _ = _ := by rw [normalizedGauss_norm_sq χ hχ]
  rw [hfour]

attribute [local instance] OAI.Ostmann.gaussFourthFintype
theorem nonprincipal_fourier_fourth_bound {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ b, additiveFourier f b = (w b : ℂ)) (hw : ∀ b, 0 ≤ w b) :
    (∑ χ ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
      ∑ a : ZMod p, ‖additiveFourier (fun x => f x * χ x) a‖ ^ 4) ≤
      ((p : ℝ)⁻¹) ^ 2 *
        (2 * (p : ℝ) * (Fintype.card (ZMod p)ˣ : ℝ) *
          (∑ b : ZMod p, w b ^ 2) ^ 2 + 3 * (∑ b : ZMod p, w b) ^ 4) := by
  classical
  let S : Finset (MulChar (ZMod p) ℂ) := Finset.univ.erase 1
  have hinv : (∑ χ ∈ S, ∑ a : ZMod p, ‖weightedCharacterSum w χ⁻¹ a‖ ^ 4) =
      ∑ χ ∈ S, ∑ a : ZMod p, ‖weightedCharacterSum w χ a‖ ^ 4 := by
    apply Finset.sum_bij (fun χ _ => χ⁻¹)
    · intro χ hχ
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      exact (Finset.mem_erase.mp hχ).1 (inv_injective (by simpa only [inv_one] using h))
    · intro χ _ ψ _ h
      exact inv_injective h
    · intro χ hχ
      refine ⟨χ⁻¹, ?_, inv_inv χ⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      exact (Finset.mem_erase.mp hχ).1 (inv_injective (by simpa only [inv_one] using h))
    · intro χ _
      rfl
  calc
    _ = ((p : ℝ)⁻¹) ^ 2 *
        (∑ χ ∈ S, ∑ a : ZMod p, ‖weightedCharacterSum w χ⁻¹ a‖ ^ 4) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact additiveFourier_character_norm_four f w hf χ (Finset.mem_erase.mp hχ).1 a
    _ = ((p : ℝ)⁻¹) ^ 2 *
        (∑ χ ∈ S, ∑ a : ZMod p, ‖weightedCharacterSum w χ a‖ ^ 4) := by rw [hinv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (nonprincipal_fourth_moment_bound w hw) (sq_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FourthMomentFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summing the nonprincipal fourth moment over bottom-pair characters

Only the common mass bound, the maximum squared mass, and the total
squared mass of the nonnegative Fourier weights enter this calculation.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.fourthFamilyFintype
attribute [local instance] OAI.Ostmann.fourthFamilyDecidableEq
theorem nonprincipal_fourth_family_bound {p : ℕ} [Fact p.Prime]
    (f : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (w : MulChar (ZMod p) ℂ → ZMod p → ℝ)
    (hf : ∀ χ a, additiveFourier (f χ) a = (w χ a : ℂ))
    (hw : ∀ χ a, 0 ≤ w χ a)
    (J R S : ℝ) (hR : 0 ≤ R)
    (hmass : ∀ χ, (∑ a : ZMod p, w χ a) ≤ J)
    (hmax : ∀ χ, (∑ a : ZMod p, w χ a ^ 2) ≤ R)
    (htotal : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, w χ a ^ 2) ≤ S) :
    (∑ χ : MulChar (ZMod p) ℂ,
      ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖additiveFourier (fun x => f χ x * α x) a‖ ^ 4) ≤
      2 * ((Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ)) * R * S +
        3 * ((Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ) ^ 2) * J ^ 4 := by
  classical
  let r : MulChar (ZMod p) ℂ → ℝ := fun χ => ∑ a : ZMod p, w χ a ^ 2
  have hr (χ : MulChar (ZMod p) ℂ) : 0 ≤ r χ :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hrs : (∑ χ : MulChar (ZMod p) ℂ, r χ ^ 2) ≤ R * S := by
    calc
      _ ≤ ∑ χ : MulChar (ZMod p) ℂ, R * r χ := by
        apply Finset.sum_le_sum
        intro χ _
        have hm : r χ ≤ R := hmax χ
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hm (hr χ)
      _ = R * ∑ χ : MulChar (ZMod p) ℂ, r χ := (Finset.mul_sum _ _ _).symm
      _ ≤ R * S := mul_le_mul_of_nonneg_left htotal hR
  have hm (χ : MulChar (ZMod p) ℂ) : (∑ a : ZMod p, w χ a) ^ 4 ≤ J ^ 4 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => hw χ a)) (hmass χ) 4
  have hms : (∑ χ : MulChar (ZMod p) ℂ, (∑ a : ZMod p, w χ a) ^ 4) ≤
      (Fintype.card (ZMod p)ˣ : ℝ) * J ^ 4 := by
    calc
      _ ≤ ∑ _χ : MulChar (ZMod p) ℂ, J ^ 4 := Finset.sum_le_sum (fun χ _ => hm χ)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_mulChar_eq_card_units]
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  calc
    _ ≤ ∑ χ : MulChar (ZMod p) ℂ,
        ((p : ℝ)⁻¹) ^ 2 *
          (2 * (p : ℝ) * (Fintype.card (ZMod p)ˣ : ℝ) * r χ ^ 2 +
            3 * (∑ a : ZMod p, w χ a) ^ 4) := by
      exact Finset.sum_le_sum fun χ _ => nonprincipal_fourier_fourth_bound (f χ) (w χ) (hf χ) (hw χ)
    _ = ((p : ℝ)⁻¹) ^ 2 *
        (2 * (p : ℝ) * (Fintype.card (ZMod p)ˣ : ℝ) *
          (∑ χ : MulChar (ZMod p) ℂ, r χ ^ 2) +
          3 * (∑ χ : MulChar (ZMod p) ℂ, (∑ a : ZMod p, w χ a) ^ 4)) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ ((p : ℝ)⁻¹) ^ 2 *
        (2 * (p : ℝ) * (Fintype.card (ZMod p)ˣ : ℝ) * (R * S) +
          3 * ((Fintype.card (ZMod p)ˣ : ℝ) * J ^ 4)) := by
      gcongr
    _ = _ := by field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TwistCauchy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cauchy--Schwarz for the two-bad quartet twists

The two character changes are permutations. After excluding principal
twists, the two squared energies are exactly the fourth-moment sums.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.twistCauchyFintype
attribute [local instance] OAI.Ostmann.twistCauchyDecidableEq
private theorem sum_nonprincipal_twist {p : ℕ} [Fact p.Prime]
    (ν : MulChar (ZMod p) ℂ) (f : MulChar (ZMod p) ℂ → ℝ) :
    (∑ ψ : MulChar (ZMod p) ℂ, if ν * ψ⁻¹ ≠ 1 then f (ν * ψ⁻¹) else 0) =
      ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1, f α := by
  classical
  let e := (Equiv.inv (MulChar (ZMod p) ℂ)).trans (Equiv.mulLeft ν)
  calc
    _ = ∑ α : MulChar (ZMod p) ℂ, if α ≠ 1 then f α else 0 :=
      e.bijective.sum_comp (fun α => if α ≠ 1 then f α else 0)
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext α
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        and_true]

/-- The nonprincipal part of the two-bad sum is controlled by two fourth moments. -/
theorem two_bad_twist_cauchy {p : ℕ} [Fact p.Prime]
    (F G : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (ν : MulChar (ZMod p) ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
        ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0) ^ 2 ≤
      (∑ χ : MulChar (ZMod p) ℂ,
        ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
          ∑ a : ZMod p, ‖F χ α a‖ ^ 4) *
      (∑ ψ : MulChar (ZMod p) ℂ,
        ∑ β ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
          ∑ a : ZMod p, ‖G ψ β a‖ ^ 4) := by
  classical
  let u : MulChar (ZMod p) ℂ × (MulChar (ZMod p) ℂ × ZMod p) → ℝ :=
    fun t => if ν * t.2.1⁻¹ ≠ 1 then ‖F t.1 (ν * t.2.1⁻¹) t.2.2‖ ^ 2 else 0
  let v : MulChar (ZMod p) ℂ × (MulChar (ZMod p) ℂ × ZMod p) → ℝ :=
    fun t => if ν⁻¹ * t.1⁻¹ ≠ 1 then ‖G t.2.1 (ν⁻¹ * t.1⁻¹) (-t.2.2)‖ ^ 2 else 0
  have hprod : (∑ t, u t * v t) =
      ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
        if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
          ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0 := by
    simp only [Fintype.sum_prod_type, u, v]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro ψ _
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp_all
  have hu : (∑ t, u t ^ 2) =
      ∑ χ : MulChar (ZMod p) ℂ,
        ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
          ∑ a : ZMod p, ‖F χ α a‖ ^ 4 := by
    simp only [Fintype.sum_prod_type, u, ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      ← pow_mul, (show (2 : ℕ) * 2 = 4 by decide)]
    apply Finset.sum_congr rfl
    intro χ _
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    exact sum_nonprincipal_twist ν (fun α => ∑ a : ZMod p, ‖F χ α a‖ ^ 4)
  have hv : (∑ t, v t ^ 2) =
      ∑ ψ : MulChar (ZMod p) ℂ,
        ∑ β ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
          ∑ a : ZMod p, ‖G ψ β a‖ ^ 4 := by
    simp only [Fintype.sum_prod_type, v, ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      ← pow_mul, (show (2 : ℕ) * 2 = 4 by decide)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ψ _
    have hneg (β : MulChar (ZMod p) ℂ) : (∑ a : ZMod p, ‖G ψ β (-a)‖ ^ 4) =
        ∑ a : ZMod p, ‖G ψ β a‖ ^ 4 :=
      (Equiv.neg (ZMod p)).bijective.sum_comp (fun a => ‖G ψ β a‖ ^ 4)
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, hneg]
    exact sum_nonprincipal_twist ν⁻¹ (fun β => ∑ a : ZMod p, ‖G ψ β a‖ ^ 4)
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  rwa [hprod, hu, hv] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MellinDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mellin Parseval on a multiplicative diagonal

This is the finite interchange of Mellin expansion and a weighted sum
used at the beginning of the proof of the uniform estimate `src42`.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.instFintypeMulCharZModComplexOfFactPrime_solutions_1
theorem mellinCoefficient_of_expansion {p : ℕ} [Fact p.Prime]
    (c : MulChar (ZMod p) ℂ → ℂ) (f : (ZMod p)ˣ → ℂ)
    (hf : ∀ z, f z = ∑ χ : MulChar (ZMod p) ℂ, c χ * χ z)
    (ρ : MulChar (ZMod p) ℂ) : mellinCoefficient f ρ = c ρ := by
  classical
  have hcard : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold mellinCoefficient
  simp_rw [hf, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  calc
    _ = ∑ χ : MulChar (ZMod p) ℂ, (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ *
        (c χ * ∑ z : (ZMod p)ˣ, χ z * conj (ρ z)) := by
      apply Finset.sum_congr rfl
      intro χ _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = c ρ := by
      simp_rw [mellin_orthogonality]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
      field_simp

theorem mellinDiagonal_expansion {p : ℕ} [Fact p.Prime]
    (H : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) (v : (ZMod p)ˣ → ℂ) (lam : (ZMod p)ˣ) :
    mellinDiagonal H v lam = ∑ χ : MulChar (ZMod p) ℂ,
      mellinDiagonalCoefficient H v χ * χ lam := by
  have hH (d t : (ZMod p)ˣ) : H d t =
      ∑ χ : MulChar (ZMod p) ℂ, mellinCoefficient (H d) χ * χ t :=
    (mellin_inversion (H d) t).symm
  unfold mellinDiagonal mellinDiagonalCoefficient
  simp_rw [hH, Units.val_mul, map_mul, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem mellinDiagonal_coefficient {p : ℕ} [Fact p.Prime]
    (H : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) (v : (ZMod p)ˣ → ℂ)
    (χ : MulChar (ZMod p) ℂ) :
    mellinCoefficient (mellinDiagonal H v) χ = mellinDiagonalCoefficient H v χ :=
  mellinCoefficient_of_expansion _ _ (mellinDiagonal_expansion H v) χ

theorem mellinDiagonal_parseval {p : ℕ} [Fact p.Prime]
    (H : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) (v : (ZMod p)ˣ → ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ‖mellinDiagonalCoefficient H v χ‖ ^ 2) =
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        ∑ lam : (ZMod p)ˣ, ‖mellinDiagonal H v lam‖ ^ 2 := by
  simpa only [mellinDiagonal_coefficient] using mellin_parseval (mellinDiagonal H v)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ReciprocalTwist
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The reciprocal twist used in the uniform Mellin estimate

Inversion preserves the finite-field squared norm. The mean of the
reciprocal twist is exactly an additive Fourier coefficient of the
original multiplicatively twisted test.
-/

namespace Ostmann

open scoped BigOperators

theorem reciprocalTwist_zero {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    reciprocalTwist g η a 0 = 0 := by
  simp only [reciprocalTwist, inv_zero, hg, zero_mul]

theorem norm_reciprocalTwist {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (η : MulChar (ZMod p) ℂ) (a x : ZMod p) :
    ‖reciprocalTwist g η a x‖ = ‖g x⁻¹‖ := by
  by_cases hx : x = 0
  · simp only [hx, reciprocalTwist_zero g hg, inv_zero, hg, norm_zero]
  · have hη : ‖η x⁻¹‖ = 1 :=
      norm_mulChar_unit η (Units.mk0 x⁻¹ (inv_ne_zero hx))
    simp only [reciprocalTwist, norm_mul, hη, mul_one]
    simp [ZMod.stdAddChar_apply]
    rw [Circle.norm_coe, mul_one]

theorem reciprocalTwist_energy {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    (∑ x : ZMod p, ‖reciprocalTwist g η a x‖ ^ 2) = ∑ x : ZMod p, ‖g x‖ ^ 2 := by
  simp_rw [norm_reciprocalTwist g hg]
  exact (Equiv.inv (ZMod p)).bijective.sum_comp (fun x : ZMod p => ‖g x‖ ^ 2)

theorem reciprocalTwist_mean {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    fieldMean (reciprocalTwist g η a) = additiveFourier (fun x => g x * η x) a := by
  rw [fieldMean_eq_sum, additiveFourier_apply]
  congr 1
  have h := (Equiv.inv (ZMod p)).bijective.sum_comp
    (fun x : ZMod p => g x * η x * ZMod.stdAddChar (-(a * x)))
  change (∑ x : ZMod p, g x⁻¹ * η x⁻¹ * ZMod.stdAddChar (-(a * x⁻¹))) =
    ∑ x : ZMod p, g x * η x * ZMod.stdAddChar (-(a * x)) at h
  simpa only [reciprocalTwist, mul_comm a] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ReciprocalCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal coordinates for the uniform Mellin estimate

The change of variables `r = lam - 1/d` is a permutation even with
the field's zero-inverse convention. Away from the singular bottom-pair
ratio, it turns reciprocal leaf arguments into a quadratic affine map.
-/

namespace Ostmann

variable {K : Type*} [Field K]

theorem reciprocal_right_argument (lam d : K) (hd : d ≠ 0) :
    (d / (lam * d - 1))⁻¹ = lam - d⁻¹ := by
  rw [inv_div]
  field_simp

theorem reciprocal_left_argument (lam d : K) (hlam : lam ≠ 0) (hd : d ≠ 0) :
    (d * (lam * d) / (lam * d - 1))⁻¹ =
      (lam - d⁻¹) - (lam - d⁻¹) ^ 2 / lam := by
  rw [inv_div]
  field_simp
  ring

theorem reciprocal_coordinate_eq_zero (lam d : K) (hd : d ≠ 0) :
    lam - d⁻¹ = 0 ↔ lam * d = 1 := by
  rw [sub_eq_zero]
  constructor
  · intro h
    rw [h, inv_mul_cancel₀ hd]
  · intro h
    exact mul_right_cancel₀ hd (by simpa only [inv_mul_cancel₀ hd] using h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ReciprocalPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The reciprocal pair identity

The character and additive phases in the reciprocal twist combine into
the diagonal bottom-pair weight. This is the pointwise calculation behind
the affine-operator parametrization of the uniform Mellin estimate.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem reciprocalTwist_pair_identity {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ) (a : ZMod p)
    (lam : (ZMod p)ˣ) (d x z : ZMod p) (hz : z ≠ 0)
    (hx : x = (lam : ZMod p) * d * z) (hdiff : x - z = d) :
    conj (η lam) * (conj (reciprocalTwist g η a z⁻¹) * reciprocalTwist g η a x⁻¹) =
      g x * conj (g z) * η d * ZMod.stdAddChar (-(a * d)) := by
  have hchar : η x = η lam * η d * η z := by rw [hx, map_mul, map_mul]
  have hphase : ZMod.stdAddChar (-(a * x)) =
      ZMod.stdAddChar (-(a * d)) * ZMod.stdAddChar (-(a * z)) := by
    rw [show -(a * x) = -(a * d) + -(a * z) by rw [← hdiff]; ring,
      AddChar.map_add_eq_mul]
  have hnlam : ‖η lam‖ = 1 := norm_mulChar_unit η lam
  have hnz : ‖η z‖ = 1 := norm_mulChar_unit η (Units.mk0 z hz)
  have hne : ‖ZMod.stdAddChar (-(a * z))‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  calc
    _ = (g x * conj (g z) * η d * ZMod.stdAddChar (-(a * d))) *
        (conj (η lam) * η lam) * (conj (η z) * η z) *
        (conj (ZMod.stdAddChar (-(a * z))) * ZMod.stdAddChar (-(a * z))) := by
      simp only [reciprocalTwist, inv_inv, hchar, hphase, map_mul]
      ring
    _ = _ := by rw [Complex.conj_mul', Complex.conj_mul', Complex.conj_mul', hnlam, hnz, hne]; norm_num

theorem reciprocal_diagonal_pair {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (η : MulChar (ZMod p) ℂ)
    (a : ZMod p) (lam : (ZMod p)ˣ) (d : ZMod p) :
    fieldBottomPair g d ((lam : ZMod p) * d) * η d * ZMod.stdAddChar (-(a * d)) =
      conj (η lam) *
        (conj (reciprocalTwist g η a ((lam : ZMod p) - d⁻¹)) *
          reciprocalTwist g η a
            (((lam : ZMod p) - d⁻¹) - ((lam : ZMod p) - d⁻¹) ^ 2 / (lam : ZMod p))) := by
  by_cases hd : d = 0
  · subst d
    have hgen : (lam : ZMod p) - (lam : ZMod p) ^ 2 / (lam : ZMod p) = 0 := by
      field_simp
      ring
    simp only [fieldBottomPair, mul_zero, zero_sub, zero_div, hg, zero_mul, inv_zero,
      sub_zero, hgen, reciprocalTwist_zero g hg, mul_zero]
  · by_cases hsing : (lam : ZMod p) * d = 1
    · have hr : (lam : ZMod p) - d⁻¹ = 0 := (reciprocal_coordinate_eq_zero _ _ hd).mpr hsing
      simp only [fieldBottomPair, hsing, sub_self, div_zero, hg, zero_mul, hr,
        reciprocalTwist_zero g hg, map_zero, mul_zero]
    · let x := d * ((lam : ZMod p) * d) / ((lam : ZMod p) * d - 1)
      let z := d / ((lam : ZMod p) * d - 1)
      have hz : z ≠ 0 := div_ne_zero hd (sub_ne_zero.mpr hsing)
      have hx : x = (lam : ZMod p) * d * z := by dsimp [x, z]; ring
      have hdiff : x - z = d := pair_coordinate_difference d ((lam : ZMod p) * d) hsing
      have hr : z⁻¹ = (lam : ZMod p) - d⁻¹ := reciprocal_right_argument _ _ hd
      have hq : x⁻¹ = ((lam : ZMod p) - d⁻¹) -
          ((lam : ZMod p) - d⁻¹) ^ 2 / (lam : ZMod p) :=
        reciprocal_left_argument _ _ (Units.ne_zero lam) hd
      simpa only [fieldBottomPair, x, z, hr, hq] using
        (reciprocalTwist_pair_identity g η a lam d x z hz hx hdiff).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ReciprocalDiagonal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The diagonal average is an affine correlation

The substitution `r = lam - 1/d` turns the weighted bottom-pair diagonal
into the affine averaging operator applied to the reciprocal twist.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem fieldBottomPair_eq_bottomPairValue {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (d t : (ZMod p)ˣ) :
    fieldBottomPair g d t = bottomPairValue g d t := by
  classical
  by_cases ht : t = 1
  · subst t
    simp [fieldBottomPair, bottomPairValue, hg]
  · simp only [bottomPairValue, ht, ite_false, if_false, fieldBottomPair]

theorem mellinDiagonal_reciprocal {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (η : MulChar (ZMod p) ℂ)
    (a : ZMod p) (lam : (ZMod p)ˣ) :
    mellinDiagonal (bottomPairValue g)
      (fun d : (ZMod p)ˣ => η d * ZMod.stdAddChar (-(a * (d : ZMod p)))) lam =
        conj (η lam) *
          affineAverage (fun r : (ZMod p)ˣ => conj (reciprocalTwist g η a r))
            (reciprocalTwist g η a) ((lam : ZMod p)⁻¹) := by
  classical
  let G := reciprocalTwist g η a
  let H : ZMod p → ℂ := fun d =>
    fieldBottomPair g d ((lam : ZMod p) * d) * η d * ZMod.stdAddChar (-(a * d))
  let F : ZMod p → ℂ := fun r => conj (G r) * G (r - r ^ 2 / (lam : ZMod p))
  have hH0 : H 0 = 0 := by simp [H, fieldBottomPair, hg]
  have hF0 : F 0 = 0 := by simp [F, G, reciprocalTwist_zero g hg]
  have hpoint (d : ZMod p) : H d = conj (η lam) * F ((lam : ZMod p) - d⁻¹) :=
    reciprocal_diagonal_pair g hg η a lam d
  have hreindex : (∑ d : ZMod p, F ((lam : ZMod p) - d⁻¹)) = ∑ r : ZMod p, F r :=
    (reciprocalCoordinates (lam : ZMod p)).bijective.sum_comp F
  calc
    _ = (p : ℂ)⁻¹ * ∑ d : (ZMod p)ˣ, H d := by
      unfold mellinDiagonal
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [H]
      rw [← Units.val_mul, fieldBottomPair_eq_bottomPairValue g hg]
      ring
    _ = (p : ℂ)⁻¹ * ∑ d : ZMod p, H d := by
      rw [sum_units_eq_sum_of_zero H hH0]
    _ = conj (η lam) * ((p : ℂ)⁻¹ * ∑ r : ZMod p, F r) := by
      simp_rw [hpoint]
      rw [← Finset.mul_sum, hreindex]
      ring
    _ = _ := by
      rw [← sum_units_eq_sum_of_zero F hF0]
      simp only [F, G, affineAverage, affineGenerator, div_eq_mul_inv]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_UniformMellin
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The uniform Mellin estimate

The positive-difference form of equation `src42` follows by combining
Mellin Parseval on the diagonal with the reciprocal affine bound.
-/

namespace Ostmann

open scoped BigOperators

theorem mellinDiagonalCoefficient_eq_fourier {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (η χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    mellinDiagonalCoefficient (bottomPairValue g)
      (fun d : (ZMod p)ˣ => η d * ZMod.stdAddChar (-(a * (d : ZMod p)))) χ =
        additiveFourier (fun d => pairAutocorrelation g χ d * χ d * η d) a := by
  let F : ZMod p → ℂ := fun d =>
    pairAutocorrelation g χ d * χ d * η d * ZMod.stdAddChar (-(a * d))
  have hF0 : F 0 = 0 := by simp only [F, MulChar.map_zero, mul_zero, zero_mul]
  unfold mellinDiagonalCoefficient
  calc
    _ = (p : ℂ)⁻¹ * ∑ d : (ZMod p)ˣ, F d := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      rw [bottomPair_mellin_autocorrelation]
      dsimp [F, pairAutocorrelation]
      ring
    _ = (p : ℂ)⁻¹ * ∑ d : ZMod p, F d := by
      rw [sum_units_eq_sum_of_zero F hF0]
    _ = _ := by simp only [F, additiveFourier_apply, mul_comm a]

attribute [local instance] OAI.Ostmann.instFintypeMulCharZModComplexOfFactPrime_solutions_2
theorem bottomPair_diagonal_norm_bound {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ,
      ‖mellinDiagonalCoefficient (bottomPairValue g)
        (fun d : (ZMod p)ˣ => η d * ZMod.stdAddChar (-(a * (d : ZMod p)))) χ‖ ^ 2) ≤
      ((p : ℝ) / ((p : ℝ) - 1)) *
        (‖additiveFourier (fun x => g x * η x) a‖ ^ 4 + Real.sqrt (3 / (p : ℝ))) := by
  let G := reciprocalTwist g η a
  have hG0 : G 0 = 0 := reciprocalTwist_zero g hg η a
  have hG : (∑ x : ZMod p, ‖G x‖ ^ 2) ≤ (p : ℝ) := by
    rw [show (∑ x : ZMod p, ‖G x‖ ^ 2) = ∑ x : ZMod p, ‖g x‖ ^ 2 from
      reciprocalTwist_energy g hg η a]
    exact henergy
  have hc : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  rw [mellinDiagonal_parseval]
  simp_rw [mellinDiagonal_reciprocal g hg, norm_mul, Complex.norm_conj,
    norm_mulChar_unit, one_mul]
  have hinv : (∑ t : (ZMod p)ˣ,
      ‖affineAverage (fun r : (ZMod p)ˣ => starRingEnd ℂ (G r)) G ((t : ZMod p)⁻¹)‖ ^ 2) =
      ∑ t : (ZMod p)ˣ, ‖affineAverage (fun r : (ZMod p)ˣ => starRingEnd ℂ (G r)) G t‖ ^ 2 := by
    have h := (Equiv.inv (ZMod p)ˣ).bijective.sum_comp
      (fun t : (ZMod p)ˣ => ‖affineAverage (fun r : (ZMod p)ˣ => starRingEnd ℂ (G r)) G t‖ ^ 2)
    change (∑ t : (ZMod p)ˣ,
      ‖affineAverage (fun r : (ZMod p)ˣ => starRingEnd ℂ (G r)) G ((t⁻¹ : (ZMod p)ˣ) : ZMod p)‖ ^ 2) = _ at h
    simpa only [Units.val_inv_eq_inv_val] using h
  change (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
    (∑ t : (ZMod p)ˣ, ‖affineAverage (fun r : (ZMod p)ˣ => starRingEnd ℂ (G r)) G
      ((t : ZMod p)⁻¹)‖ ^ 2) ≤ _
  rw [hinv, hc]
  have h := affineAverage_self_correlation_unit_bound G hG0 hG
  rw [show fieldMean G = additiveFourier (fun x => g x * η x) a from
    reciprocalTwist_mean g η a] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- Equation `src42` with the positive difference convention. -/
theorem uniform_mellin_bound {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ,
      ‖additiveFourier (fun d => pairAutocorrelation g χ d * χ d * η d) a‖ ^ 2) ≤
      ((p : ℝ) / ((p : ℝ) - 1)) *
        (‖additiveFourier (fun x => g x * η x) a‖ ^ 4 + Real.sqrt (3 / (p : ℝ))) := by
  simpa only [mellinDiagonalCoefficient_eq_fourier] using
    bottomPair_diagonal_norm_bound g hg henergy η a

/-- The mixed Fourier hypothesis gives the paper's explicit epsilon bound. -/
theorem uniform_mellin_bound_of_fourier_bound {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : ∀ (χ : MulChar (ZMod p) ℂ) (a : ZMod p),
      ‖additiveFourier (fun x => g x * χ x) a‖ ≤ ε)
    (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ,
      ‖additiveFourier (fun d => pairAutocorrelation g χ d * χ d * η d) a‖ ^ 2) ≤
      ((p : ℝ) / ((p : ℝ) - 1)) * (ε ^ 4 + Real.sqrt (3 / (p : ℝ))) := by
  have hden : 0 ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    linarith
  exact (uniform_mellin_bound g hg henergy η a).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hε η a) 4) le_rfl)
      (div_nonneg (Nat.cast_nonneg p) hden))

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

theorem MixedFourierBound.conj {p : ℕ} [Fact p.Prime]
    {g : ZMod p → ℂ} {ε : ℝ} (h : MixedFourierBound g ε) :
    MixedFourierBound (fun x => conj (g x)) ε := by
  intro χ a
  have hfun : (fun x => conj (g x) * χ x) =
      (fun x => conj (g x * χ⁻¹ x)) := by
    funext x
    have hc := MulChar.star_apply' χ⁻¹ x
    change conj (χ⁻¹ x) = _ at hc
    simp only [inv_inv] at hc
    rw [map_mul, hc]
  rw [hfun, additiveFourier_conj, Complex.norm_conj]
  exact h χ⁻¹ (-a)

theorem MixedFourierBound.unit_mul {p : ℕ} [Fact p.Prime]
    {g : ZMod p → ℂ} {ε : ℝ} (h : MixedFourierBound g ε) (u : (ZMod p)ˣ) :
    MixedFourierBound (fun x => g ((u : ZMod p) * x)) ε := by
  intro χ a
  have hunit : χ ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * χ (u : ZMod p) = 1 := by
    rw [← map_mul, ← Units.val_mul]
    simp only [inv_mul_cancel, Units.val_one, map_one]
  have hfun : (fun x => g ((u : ZMod p) * x) * χ x) =
      (fun x => χ ((u⁻¹ : (ZMod p)ˣ) : ZMod p) *
        ((g ((u : ZMod p) * x)) * χ ((u : ZMod p) * x))) := by
    funext x
    rw [map_mul]
    calc
      _ = (χ ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * χ (u : ZMod p)) *
          (g ((u : ZMod p) * x) * χ x) := by rw [hunit, one_mul]
      _ = _ := by ring
  rw [hfun, additiveFourier_const_mul,
    additiveFourier_unit_mul (fun x => g x * χ x), norm_mul,
    norm_mulChar_unit χ u⁻¹, one_mul]
  exact h χ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier estimates for quartet terms

The friendly term follows from the uniform Mellin estimate and Parseval
energy. A nonprincipal Gauss transform also has the uniform maximum used
when exactly one of the two quartet twists is principal.
-/

namespace Ostmann

open scoped BigOperators

theorem weightedCharacterSum_norm_le {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ b, 0 ≤ w b)
    (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    ‖weightedCharacterSum w χ a‖ ≤ ∑ b : ZMod p, w b := by
  unfold weightedCharacterSum
  calc
    _ ≤ ∑ b : ZMod p, ‖(w b : ℂ) * χ (a - b)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw b)]
      exact mul_le_of_le_one_right (hw b) (norm_mulChar_le_one χ (a - b))

theorem nonprincipal_fourier_norm_sq_le {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ b, additiveFourier f b = (w b : ℂ)) (hw : ∀ b, 0 ≤ w b)
    (J : ℝ) (hJ : (∑ b : ZMod p, w b) ≤ J)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    ‖additiveFourier (fun x => f x * χ x) a‖ ^ 2 ≤ (p : ℝ)⁻¹ * J ^ 2 := by
  have hm := (weightedCharacterSum_norm_le w hw χ⁻¹ a).trans hJ
  have hfour : ‖additiveFourier (fun x => f x * χ x) a‖ ^ 4 ≤
      ((p : ℝ)⁻¹) ^ 2 * J ^ 4 := by
    rw [additiveFourier_character_norm_four f w hf χ hχ a]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hm 4) (sq_nonneg _)
  have hp : 0 ≤ (p : ℝ)⁻¹ * J ^ 2 := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) (sq_nonneg J)
  apply (sq_le_sq₀ (sq_nonneg _) hp).mp
  first | (convert hfour using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hfour.trans (le_of_eq (by ring)))

attribute [local instance] OAI.Ostmann.quartetFourierFintype
/-- The friendly convolution sum uses one uniform Mellin bound and one total energy. -/
theorem friendly_fourier_sum_le {p : ℕ} [Fact p.Prime]
    (P Q : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (δ C : ℝ) (hδ : 0 ≤ δ)
    (hP : ∀ (η : MulChar (ZMod p) ℂ) (a : ZMod p),
      (∑ χ : MulChar (ZMod p) ℂ,
        ‖additiveFourier (fun x => P χ x * χ x * η x) a‖ ^ 2) ≤ δ)
    (hQ : (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖additiveFourier (Q ψ) a‖ ^ 2) ≤ C)
    (η : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ) :
    (∑ a : ZMod p, ∑ ψ : MulChar (ZMod p) ℂ, ∑ χ : MulChar (ZMod p) ℂ,
      ‖additiveFourier (fun x => P χ x * χ x * η ψ x) a‖ ^ 2 *
        ‖additiveFourier (Q ψ) (-a)‖ ^ 2) ≤ δ * C := by
  have hneg (ψ : MulChar (ZMod p) ℂ) :
      (∑ a : ZMod p, ‖additiveFourier (Q ψ) (-a)‖ ^ 2) =
        ∑ a : ZMod p, ‖additiveFourier (Q ψ) a‖ ^ 2 :=
    (Equiv.neg (ZMod p)).bijective.sum_comp (fun a => ‖additiveFourier (Q ψ) a‖ ^ 2)
  calc
    _ ≤ ∑ a : ZMod p, ∑ ψ : MulChar (ZMod p) ℂ,
        δ * ‖additiveFourier (Q ψ) (-a)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro ψ _
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hP (η ψ) a) (sq_nonneg _)
    _ = δ * (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
        ‖additiveFourier (Q ψ) a‖ ^ 2) := by
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [hneg]
    _ ≤ δ * C := mul_le_mul_of_nonneg_left hQ hδ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetParseval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exact Parseval reduction for quartet averages

Two independent unit parameters are separated by Mellin Parseval.
The remaining difference convolution is diagonalized by additive Parseval.
All normalizations are the probability normalizations of Section 6.
-/

namespace Ostmann

open scoped BigOperators

theorem additiveFourier_reflection {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => f (-x)) a = additiveFourier f (-a) := by
  rw [additiveFourier_apply, additiveFourier_apply]
  congr 1
  calc
    _ = ∑ x : ZMod p, f (-(-x)) * ZMod.stdAddChar (-((-x) * a)) :=
      ((Equiv.neg (ZMod p)).bijective.sum_comp
        (fun x => f (-x) * ZMod.stdAddChar (-(x * a)))).symm
    _ = _ := by simp

theorem additiveFourier_differenceConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (additiveDifferenceConvolution f g) a =
      additiveFourier f a * additiveFourier g (-a) := by
  have heq : additiveDifferenceConvolution f g =
      additiveConvolution f (fun x => g (-x)) := by
    funext y
    simp only [additiveDifferenceConvolution, additiveConvolution, neg_sub]
  rw [heq, additiveFourier_convolution, additiveFourier_reflection]

theorem differenceConvolution_parseval {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) :
    (p : ℝ)⁻¹ * (∑ y : ZMod p, ‖additiveDifferenceConvolution f g y‖ ^ 2) =
      ∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2 * ‖additiveFourier g (-a)‖ ^ 2 := by
  rw [← additiveFourier_parseval]
  simp only [additiveFourier_differenceConvolution, norm_mul, mul_pow]

attribute [local instance] OAI.Ostmann.quartetParsevalFintype
/-- Parseval for coefficients given by an explicit Mellin synthesis. -/
theorem mellin_synthesis_parseval {p : ℕ} [Fact p.Prime]
    (c : MulChar (ZMod p) ℂ → ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ, ‖∑ χ : MulChar (ZMod p) ℂ, c χ * χ z‖ ^ 2) =
        ∑ χ : MulChar (ZMod p) ℂ, ‖c χ‖ ^ 2 := by
  rw [← mellin_parseval]
  congr 1
  funext χ
  rw [mellinCoefficient_of_expansion c _ (fun _ => rfl)]

/-- Two independent held parameters separate both Mellin indices. -/
theorem mellin_product_synthesis_parseval {p : ℕ} [Fact p.Prime]
    (c : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ, (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        ∑ t : (ZMod p)ˣ,
          ‖∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ,
            c χ ψ * χ z * ψ t‖ ^ 2) =
      ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ‖c χ ψ‖ ^ 2 := by
  have hexp (z t : (ZMod p)ˣ) :
      (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, c χ ψ * χ z * ψ t) =
        ∑ ψ : MulChar (ZMod p) ℂ, (∑ χ : MulChar (ZMod p) ℂ, c χ ψ * χ z) * ψ t := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  simp_rw [hexp, mellin_synthesis_parseval]
  rw [Finset.sum_comm, Finset.mul_sum]
  simp_rw [mellin_synthesis_parseval]
  rw [Finset.sum_comm]

/-- Exact reduction to the Fourier sum used for all four quartet orientations. -/
theorem quartetSynthesis_parseval {p : ℕ} [Fact p.Prime]
    (f g : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (α β : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ) :
    (p : ℝ)⁻¹ * (∑ y : ZMod p,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ z : (ZMod p)ˣ,
        (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ t : (ZMod p)ˣ, ‖quartetSynthesis f g α β y z t‖ ^ 2)) =
      ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
        ‖additiveFourier (fun d => f χ d * α χ ψ d) a‖ ^ 2 *
          ‖additiveFourier (fun e => g ψ e * β χ ψ e) (-a)‖ ^ 2 := by
  simp only [quartetSynthesis, mellin_product_synthesis_parseval]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ψ _
  exact differenceConvolution_parseval _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact Mellin expansion of the two-bad quartet term

The pair function is zero at a zero difference or ratio. The extra
multiplicative character also kills zero differences, so the full-field
convolution and the valid-pair formula agree exactly.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.quartetExpansionFintype
theorem fieldBottomPairValue_expansion {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) (hd : d ≠ 0) :
    fieldBottomPairValue g d t =
      ∑ χ : MulChar (ZMod p) ℂ, pairAutocorrelation g χ d * χ t := by
  classical
  by_cases ht : t = 0
  · simp [fieldBottomPairValue, ht, MulChar.map_zero]
  · have h := mellin_inversion (bottomPairValue g (Units.mk0 d hd)) (Units.mk0 t ht)
    simp only [bottomPair_mellin_autocorrelation, Units.val_mk0] at h
    simpa only [fieldBottomPairValue, hd, ht, dite_false, pairAutocorrelation] using h.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetOrientations
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The four quartet orientation formulas

A friendly side uses its own difference, and a bad side uses the reciprocal
of the other difference. The twists below are exactly the four rows in
`tree-twisted-convolution`.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.quartetOrientationsFintype
theorem quartetParameterValue_eq_synthesis {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ)
    (y : ZMod p) (z t : (ZMod p)ˣ) :
    quartetParameterValue g h left right ν y z t =
      quartetSynthesis (pairAutocorrelation g) (pairAutocorrelation h)
        (quartetLeftTwist left right ν) (quartetRightTwist left right ν) y z t := by
  classical
  unfold quartetParameterValue quartetSynthesis additiveDifferenceConvolution
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (MulChar (ZMod p) ℂ)))
    (t := (Finset.univ : Finset (ZMod p)))]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d = 0
  · simp [hd, fieldBottomPairValue, quartetLeftTwist, MulChar.map_zero]
  by_cases he : d - y = 0
  · simp [he, fieldBottomPairValue, quartetRightTwist, MulChar.map_zero]
  rw [fieldBottomPairValue_expansion g d _ hd,
    fieldBottomPairValue_expansion h (d - y) _ he]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  apply Finset.sum_congr rfl
  intro ψ _
  cases left <;> cases right <;>
    simp only [quartetLeftRatio, quartetRightRatio, quartetLeftTwist, quartetRightTwist,
      Bool.false_eq_true, ite_false, if_false, ite_true, if_true, mul_one,
      div_eq_mul_inv, map_mul, ← MulChar.inv_apply', MulChar.coeToFun_mul, Pi.mul_apply] <;> ring

/-- All orientation choices have precisely the two-twist Fourier norm. -/
theorem quartetParameterValue_parseval {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ) :
    (p : ℝ)⁻¹ * (∑ y : ZMod p,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ z : (ZMod p)ˣ,
        (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ t : (ZMod p)ˣ, ‖quartetParameterValue g h left right ν y z t‖ ^ 2)) =
      ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
        ‖additiveFourier (fun d => pairAutocorrelation g χ d *
          quartetLeftTwist left right ν χ ψ d) a‖ ^ 2 *
        ‖additiveFourier (fun e => pairAutocorrelation h ψ e *
          quartetRightTwist left right ν χ ψ e) (-a)‖ ^ 2 := by
  simp_rw [quartetParameterValue_eq_synthesis]
  exact quartetSynthesis_parseval _ _ _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_FriendlyQuartet
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The friendly quartet estimate

The exact held-parameter average is bounded by the uniform Mellin estimate
on one side and total Fourier energy on the other side.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.friendlyQuartetFintype
theorem left_friendly_fourier_sum_le {p : ℕ} [Fact p.Prime]
    (P Q : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (δ S : ℝ) (hδ : 0 ≤ δ)
    (hP : ∀ (η : MulChar (ZMod p) ℂ) (a : ZMod p),
      (∑ χ : MulChar (ZMod p) ℂ,
        ‖additiveFourier (fun x => P χ x * χ x * η x) a‖ ^ 2) ≤ δ)
    (hQ : (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (Q ψ) a‖ ^ 2) ≤ S)
    (right : Bool) (ν : MulChar (ZMod p) ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (fun x => P χ x * quartetLeftTwist true right ν χ ψ x) a‖ ^ 2 *
      ‖additiveFourier (fun x => Q ψ x * quartetRightTwist true right ν χ ψ x) (-a)‖ ^ 2) ≤
        δ * S := by
  let η : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ :=
    fun ψ => ν * (if right then 1 else ψ⁻¹)
  let Q' : MulChar (ZMod p) ℂ → ZMod p → ℂ :=
    fun ψ x => Q ψ x * (ν⁻¹ * (if right then ψ else 1)) x
  have hQ' : (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (Q' ψ) a‖ ^ 2) ≤ S := by
    apply le_trans _ hQ
    exact Finset.sum_le_sum fun ψ _ =>
      additiveFourier_character_energy_le (Q ψ) (ν⁻¹ * (if right then ψ else 1))
  have hleft (χ ψ : MulChar (ZMod p) ℂ) :
      (fun x => P χ x * quartetLeftTwist true right ν χ ψ x) =
        (fun x => P χ x * χ x * η ψ x) := by
    funext x
    simp only [quartetLeftTwist, ite_true, if_true, η, MulChar.coeToFun_mul, Pi.mul_apply]
    ring
  have hright (χ ψ : MulChar (ZMod p) ℂ) :
      (fun x => Q ψ x * quartetRightTwist true right ν χ ψ x) = Q' ψ := by
    simp only [quartetRightTwist, ite_true, if_true, mul_one, Q']
  simp_rw [hleft, hright]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (MulChar (ZMod p) ℂ)))
    (t := (Finset.univ : Finset (ZMod p)))]
  exact friendly_fourier_sum_le P Q' δ S hδ hP hQ' η

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetSymmetry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Interchanging the two bottom pairs

Swapping the pairs inverts the quotient character and negates additive
frequency. This supplies the right-friendly estimate from the left one.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.quartetSymmetryFintype
theorem quartetFourierEnergy_swap {p : ℕ} [Fact p.Prime]
    (P Q : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (left right : Bool) (ν : MulChar (ZMod p) ℂ) :
    quartetFourierEnergy P Q left right ν = quartetFourierEnergy Q P right left ν⁻¹ := by
  have hL (χ ψ : MulChar (ZMod p) ℂ) :
      quartetLeftTwist left right ν χ ψ = quartetRightTwist right left ν⁻¹ ψ χ := by
    cases left <;> cases right <;>
      simp [quartetLeftTwist, quartetRightTwist, mul_comm, mul_left_comm, mul_assoc]
  have hR (χ ψ : MulChar (ZMod p) ℂ) :
      quartetRightTwist left right ν χ ψ = quartetLeftTwist right left ν⁻¹ ψ χ := by
    cases left <;> cases right <;>
      simp [quartetLeftTwist, quartetRightTwist, mul_comm, mul_assoc]
  unfold quartetFourierEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ψ _
  apply Finset.sum_congr rfl
  intro χ _
  simp_rw [hL, hR]
  calc
    _ = ∑ a : ZMod p,
        ‖additiveFourier (fun x => Q ψ x * quartetLeftTwist right left ν⁻¹ ψ χ x) (-a)‖ ^ 2 *
        ‖additiveFourier (fun x => P χ x * quartetRightTwist right left ν⁻¹ ψ χ x) a‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _
    _ = _ := by
      simpa only [Equiv.neg_apply, neg_neg] using
        (Equiv.neg (ZMod p)).bijective.sum_comp (fun a =>
          ‖additiveFourier (fun x => Q ψ x * quartetLeftTwist right left ν⁻¹ ψ χ x) a‖ ^ 2 *
          ‖additiveFourier (fun x => P χ x * quartetRightTwist right left ν⁻¹ ψ χ x) (-a)‖ ^ 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_DifferenceMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Means of nonnegative difference convolutions

Removing the zero difference can only decrease the sum. This supplies
the mean bounds for the nonnegative quartet majorants in Section 6.
-/

namespace Ostmann

open scoped BigOperators

theorem differenceMoment_nonneg {p : ℕ} [NeZero p]
    (f g : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (y : ZMod p) :
    0 ≤ differenceMoment f g y :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hf _) (hg _))

theorem sum_differenceMoment {p : ℕ} [NeZero p] (f g : ZMod p → ℝ) :
    (∑ y : ZMod p, differenceMoment f g y) =
      (∑ x : ZMod p, f x) * ∑ z : ZMod p, g z := by
  have hshift (x : ZMod p) : (∑ y : ZMod p, g (x - y)) = ∑ z : ZMod p, g z := by
    simpa [sub_eq_add_neg] using
      ((Equiv.neg (ZMod p)).trans (Equiv.addLeft x)).bijective.sum_comp g
  unfold differenceMoment
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hshift]
  rw [Finset.sum_mul]

theorem sum_units_differenceMoment_le {p : ℕ} [Fact p.Prime]
    (f g : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    (∑ y : (ZMod p)ˣ, differenceMoment f g y) ≤
      (∑ x : ZMod p, f x) * ∑ z : ZMod p, g z := by
  classical
  rw [← sum_differenceMoment]
  exact OAI.sum_le_sum_of_injOn (fun y : (ZMod p)ˣ => (y : ZMod p))
    Units.val_injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
    (fun y _ _ => differenceMoment_nonneg f g hf hg y)

theorem mean_units_differenceMoment_le {p : ℕ} [Fact p.Prime]
    (f g : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    ((∑ y : (ZMod p)ˣ, differenceMoment f g y) / ((p : ℝ) - 1)) / ((p : ℝ) - 1) ≤
      ((∑ x : ZMod p, f x) / ((p : ℝ) - 1)) *
        ((∑ z : ZMod p, g z) / ((p : ℝ) - 1)) := by
  have hden : 0 ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    linarith
  have h := div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (sum_units_differenceMoment_le f g hf hg) hden) hden
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquareCharacterMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summing the square-pullback majorants

Every character contributes to exactly one square fiber, and a single
fiber contains at most two characters. These are the two bounds needed
for the same-pair quartet majorant.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.squareMassFintype
attribute [local instance] OAI.Ostmann.squareMassDecidableEq
theorem squareCharacterMass_nonneg {p : ℕ} [Fact p.Prime]
    (a : MulChar (ZMod p) ℂ → ℝ) (ha : ∀ χ, 0 ≤ a χ) (ρ : MulChar (ZMod p) ℂ) :
    0 ≤ squareCharacterMass a ρ := Finset.sum_nonneg fun χ _ => ha χ

theorem squareCharacterMass_le_twice {p : ℕ} [Fact p.Prime]
    (a : MulChar (ZMod p) ℂ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ χ, a χ ≤ M) (ρ : MulChar (ZMod p) ℂ) :
    squareCharacterMass a ρ ≤ 2 * M := by
  unfold squareCharacterMass
  calc
    _ ≤ ∑ _χ ∈ Finset.univ.filter (fun χ : MulChar (ZMod p) ℂ => χ ^ 2 = ρ), M :=
      Finset.sum_le_sum fun χ _ => ha χ
    _ = ((Finset.univ.filter (fun χ : MulChar (ZMod p) ℂ => χ ^ 2 = ρ)).card : ℝ) * M := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast mulChar_square_fiber_card_le_two Finset.univ ρ) hM

theorem sum_squareCharacterMass {p : ℕ} [Fact p.Prime]
    (a : MulChar (ZMod p) ℂ → ℝ) :
    (∑ ρ : MulChar (ZMod p) ℂ, squareCharacterMass a ρ) =
      ∑ χ : MulChar (ZMod p) ℂ, a χ := by
  exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_QuartetPairMajorant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean bounds for same-pair quartet majorants

The square-fiber factor costs two for one index and costs nothing when
summed over all indices. Difference convolution then multiplies masses.
-/

namespace Ostmann

open scoped BigOperators

theorem mean_differenceMajorant_le {p : ℕ} [Fact p.Prime]
    (f g : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    (∑ y : (ZMod p)ˣ, differenceMajorant f g y) / (Fintype.card (ZMod p)ˣ : ℝ) ≤
      ((∑ x : ZMod p, f x) / (Fintype.card (ZMod p)ˣ : ℝ)) *
        ((∑ x : ZMod p, g x) / (Fintype.card (ZMod p)ˣ : ℝ)) := by
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  have h := mean_units_differenceMoment_le f g hf hg
  simp only [differenceMajorant, ← Finset.mul_sum, hU]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem samePairMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (F : MulChar (ZMod p) ℂ → ZMod p → ℝ) (R : ZMod p → ℝ)
    (hF : ∀ χ d, 0 ≤ F χ d) (hR : ∀ d, 0 ≤ R d)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : 0 ≤ samePairMajorant F R ρ y := by
  exact mul_nonneg (by positivity) (differenceMoment_nonneg _ _
    (fun d => squareCharacterMass_nonneg _ (fun χ => hF χ d) ρ) hR y)

attribute [local instance] OAI.Ostmann.samePairFintype
theorem squareCharacterMass_normalized_sum {p : ℕ} [Fact p.Prime]
    (F : MulChar (ZMod p) ℂ → ZMod p → ℝ) (ρ : MulChar (ZMod p) ℂ) :
    (∑ d : ZMod p, squareCharacterMass (fun χ => F χ d) ρ) /
      (Fintype.card (ZMod p)ˣ : ℝ) =
      squareCharacterMass (fun χ => (∑ d : ZMod p, F χ d) /
        (Fintype.card (ZMod p)ˣ : ℝ)) ρ := by
  unfold squareCharacterMass
  rw [Finset.sum_comm, Finset.sum_div]

/-- Small supremum for the same-pair majorant. -/
theorem samePairMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (F : MulChar (ZMod p) ℂ → ZMod p → ℝ) (R : ZMod p → ℝ)
    (hF : ∀ χ d, 0 ≤ F χ d) (hR : ∀ d, 0 ≤ R d)
    (M H : ℝ) (hM : 0 ≤ M)
    (hFm : ∀ χ, (∑ d : ZMod p, F χ d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ M)
    (hRm : (∑ d : ZMod p, R d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ H)
    (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, samePairMajorant F R ρ y) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ 2 * M * H := by
  have h := mean_differenceMajorant_le (fun d => squareCharacterMass (fun χ => F χ d) ρ) R
    (fun d => squareCharacterMass_nonneg _ (fun χ => hF χ d) ρ) hR
  rw [squareCharacterMass_normalized_sum] at h
  apply h.trans
  apply mul_le_mul (squareCharacterMass_le_twice _ M hM hFm ρ) hRm
  · exact div_nonneg (Finset.sum_nonneg fun d _ => hR d) (Nat.cast_nonneg _)
  · positivity

/-- Bounded sum over all indices for the same-pair majorant. -/
theorem samePairMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (F : MulChar (ZMod p) ℂ → ZMod p → ℝ) (R : ZMod p → ℝ)
    (hF : ∀ χ d, 0 ≤ F χ d) (hR : ∀ d, 0 ≤ R d)
    (S H : ℝ) (hS : 0 ≤ S)
    (hFs : (∑ χ : MulChar (ZMod p) ℂ,
      (∑ d : ZMod p, F χ d) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤ S)
    (hRm : (∑ d : ZMod p, R d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ H) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ, samePairMajorant F R ρ y) /
      (Fintype.card (ZMod p)ˣ : ℝ)) ≤ S * H := by
  calc
    _ ≤ ∑ ρ : MulChar (ZMod p) ℂ,
        squareCharacterMass (fun χ => (∑ d : ZMod p, F χ d) /
          (Fintype.card (ZMod p)ˣ : ℝ)) ρ *
        ((∑ d : ZMod p, R d) / (Fintype.card (ZMod p)ˣ : ℝ)) := by
      apply Finset.sum_le_sum
      intro ρ _
      have h := mean_differenceMajorant_le (fun d => squareCharacterMass (fun χ => F χ d) ρ) R
        (fun d => squareCharacterMass_nonneg _ (fun χ => hF χ d) ρ) hR
      rwa [squareCharacterMass_normalized_sum] at h
    _ = (∑ χ : MulChar (ZMod p) ℂ, (∑ d : ZMod p, F χ d) /
        (Fintype.card (ZMod p)ˣ : ℝ)) *
        ((∑ d : ZMod p, R d) / (Fintype.card (ZMod p)ˣ : ℝ)) := by
      rw [← Finset.sum_mul, sum_squareCharacterMass]
    _ ≤ S * H := mul_le_mul hFs hRm
      (div_nonneg (Finset.sum_nonneg fun d _ => hR d) (Nat.cast_nonneg _)) hS

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PairDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Density of one tree split

Given the parent difference, a split coordinate produces the child ratio
as a fixed unit times its inverse square. Each valid child pair therefore
has multiplicity at most two. Zero weights at zero discard invalid nodes.
-/

namespace Ostmann

open scoped BigOperators

/-- A full-field sum in ratio coordinates is exactly the difference convolution. -/
theorem pair_ratio_sum_eq {p : ℕ} [Fact p.Prime]
    (d : (ZMod p)ˣ) (f g : ZMod p → ℝ) (hf : f 0 = 0) (hg : g 0 = 0) :
    (∑ t : (ZMod p)ˣ, if t = 1 then 0 else
      f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
        g ((d : ZMod p) / ((t : ZMod p) - 1))) =
      ∑ x : ZMod p, f x * g (x - d) := by
  classical
  let H : ZMod p → ℝ := fun t => if t = 1 then 0 else
    f ((d : ZMod p) * t / (t - 1)) * g ((d : ZMod p) / (t - 1))
  have hH0 : H 0 = 0 := by simp [H, hf]
  have hunit (t : (ZMod p)ˣ) : (if t = 1 then 0 else
      f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
        g ((d : ZMod p) / ((t : ZMod p) - 1))) = H t := by
    have ht : (t : ZMod p) = 1 ↔ t = 1 := by
      constructor
      · intro h; exact Units.ext h
      · intro h; simp [h]
    simp only [H, ht]
  let e : ZMod p ≃ ZMod p :=
    (Function.Involutive.toPerm _ ratioInvolution_involutive).trans
      (Equiv.mulLeft₀ (d : ZMod p) (Units.ne_zero d))
  have he (t : ZMod p) : H t = f (e t) * g (e t - d) := by
    change H t = f ((d : ZMod p) * ratioInvolution t) *
      g ((d : ZMod p) * ratioInvolution t - d)
    by_cases ht : t = 1
    · simp [H, ratioInvolution, ht, hg]
    · have hdif : (d : ZMod p) * t / (t - 1) - d =
          (d : ZMod p) / (t - 1) := by
        have h := pair_coordinate_difference (d : ZMod p) t ht
        linear_combination h
      simp only [H, ht, ite_false, if_false, ratioInvolution, ← mul_div_assoc, hdif]
  simp_rw [hunit]
  rw [sum_units_eq_sum_of_zero H hH0]
  simp_rw [he]
  exact e.bijective.sum_comp (fun x => f x * g (x - d))

/-- Counting form of the conditional density bound at one internal node. -/
theorem pair_inverse_square_density {p : ℕ} [Fact p.Prime]
    (d K : (ZMod p)ˣ) (f g : ZMod p → ℝ)
    (hf : f 0 = 0) (hg : g 0 = 0)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (∑ m : (ZMod p)ˣ,
      let t := K * (m⁻¹) ^ 2
      if t = 1 then 0 else
        f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
          g ((d : ZMod p) / ((t : ZMod p) - 1))) ≤
      2 * ∑ x : ZMod p, f x * g (x - d) := by
  let H : (ZMod p)ˣ → ℝ := fun t => if t = 1 then 0 else
    f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
      g ((d : ZMod p) / ((t : ZMod p) - 1))
  have hn (t : (ZMod p)ˣ) : 0 ≤ H t := by
    dsimp [H]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hfn _) (hgn _)
  have h := sum_inverse_square_coset_le_twice K H hn
  rw [show (∑ t : (ZMod p)ˣ, H t) = ∑ x : ZMod p, f x * g (x - d) from
    pair_ratio_sum_eq d f g hf hg] at h
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FieldPairMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second moment of the zero-extended bottom-pair value -/

namespace Ostmann

open scoped BigOperators

theorem fieldBottomPairValue_units {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : (ZMod p)ˣ) :
    fieldBottomPairValue g d t = bottomPairValue g d t := by
  simp [fieldBottomPairValue, Units.ne_zero, Units.mk0_val]

theorem fieldPairMoment_nonneg {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) : 0 ≤ fieldPairMoment g d := by
  unfold fieldPairMoment
  positivity

theorem fieldPairMoment_eq_difference {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (d : (ZMod p)ˣ) :
    fieldPairMoment g d =
      differenceMajorant (fun x => ‖g x‖ ^ 2) (fun x => ‖g x‖ ^ 2) d := by
  unfold fieldPairMoment differenceMajorant differenceMoment
  simp_rw [fieldBottomPairValue_units]
  congr 1
  have h := pair_ratio_sum_eq d (fun x => ‖g x‖ ^ 2) (fun x => ‖g x‖ ^ 2)
    (by simp [hg]) (by simp [hg])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro t _
  unfold bottomPairValue
  split_ifs <;> simp [mul_pow]

theorem fieldPairMoment_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ d : ZMod p, fieldPairMoment g d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  rw [← sum_units_eq_sum_of_zero _ (fieldPairMoment_zero g)]
  simp_rw [fieldPairMoment_eq_difference g hg]
  apply (mean_differenceMajorant_le (fun x => ‖g x‖ ^ 2) (fun x => ‖g x‖ ^ 2)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)).trans
  rw [← pow_two]
  apply pow_le_pow_left₀ (by positivity)
  exact div_le_div_of_nonneg_right henergy (Nat.cast_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RatioParseval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parseval in the ratio of two nonzero arguments with fixed difference -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem ratioTest_sum {p : ℕ} [Fact p.Prime]
    {R : Type*} [AddCommMonoid R] (F : ZMod p → R)
    (y : (ZMod p)ˣ) (h0 : F 0 = 0) (hy : F y = 0) :
    (∑ t : (ZMod p)ˣ, if t = 1 then 0 else
      F ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1))) = ∑ d : ZMod p, F d := by
  let e : ZMod p ≃ ZMod p :=
    (Function.Involutive.toPerm _ ratioInvolution_involutive).trans
      (Equiv.mulLeft₀ (y : ZMod p) (Units.ne_zero y))
  have he (t : (ZMod p)ˣ) : (if t = 1 then 0 else
      F ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1))) = F (e t) := by
    by_cases ht : t = 1
    · simp [ht, e, ratioInvolution, hy]
    · have ht' : (t : ZMod p) ≠ 1 := fun h => ht (Units.ext h)
      simp [ht, ht', e, ratioInvolution, mul_div_assoc]
  simp_rw [he]
  have he0 : F (e 0) = 0 := by simp [e, ratioInvolution, h0]
  rw [sum_units_eq_sum_of_zero (fun t => F (e t)) he0]
  exact e.sum_comp F

theorem ratioDifferenceTransform_eq_mellin {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (h0 : F 0 = 0) (hy : F y = 0)
    (ν : MulChar (ZMod p) ℂ) :
    ratioDifferenceTransform F y ν =
      ((Fintype.card (ZMod p)ˣ : ℂ) / (p : ℂ)) *
        mellinCoefficient (ratioTest F y) ν⁻¹ := by
  have hsum := ratioTest_sum (fun d => F d * ν (d / (d - y))) y
    (by simp [h0]) (by simp [hy])
  have hterm (t : (ZMod p)ˣ) : (if t = 1 then 0 else
      F ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
        ν (((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) /
          ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1) - y))) =
      ratioTest F y t * conj (ν⁻¹ t) := by
    by_cases ht : t = 1
    · simp [ht, ratioTest]
    · have ht' : (t : ZMod p) ≠ 1 := fun h => ht (Units.ext h)
      have hden : (t : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr ht'
      have he : ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) /
          ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1) - y) = t := by
        have hd := pair_coordinate_difference (y : ZMod p) (t : ZMod p) ht'
        rw [show (y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1) - y =
          (y : ZMod p) / ((t : ZMod p) - 1) by linear_combination hd]
        field_simp
      have hn : conj (ν⁻¹ t) = ν t := by
        rw [MulChar.inv_apply_eq_inv', Complex.inv_eq_conj (norm_mulChar_unit ν t)]
        simp
      simp only [ht, ite_false, if_false, ratioTest, he, hn]
  simp_rw [hterm] at hsum
  unfold ratioDifferenceTransform mellinCoefficient
  rw [← hsum]
  have hU : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

attribute [local instance] OAI.Ostmann.ratioParsevalFintype
/-- The sum over all quotient characters costs no small-correlation hypothesis. -/
theorem ratioDifferenceTransform_parseval {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (h0 : F 0 = 0) (hy : F y = 0) :
    (∑ ν : MulChar (ZMod p) ℂ, ‖ratioDifferenceTransform F y ν‖ ^ 2) =
      (Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ) ^ 2 * ∑ d : ZMod p, ‖F d‖ ^ 2 := by
  simp_rw [ratioDifferenceTransform_eq_mellin F y h0 hy, norm_mul, norm_div,
    Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum]
  have hinv := (Equiv.inv (MulChar (ZMod p) ℂ)).bijective.sum_comp
    (fun ν => ‖mellinCoefficient (ratioTest F y) ν‖ ^ 2)
  change (∑ ν : MulChar (ZMod p) ℂ, ‖mellinCoefficient (ratioTest F y) ν⁻¹‖ ^ 2) =
    ∑ ν : MulChar (ZMod p) ℂ, ‖mellinCoefficient (ratioTest F y) ν‖ ^ 2 at hinv
  rw [hinv, mellin_parseval]
  have hsum := ratioTest_sum (fun d => ‖F d‖ ^ 2) y (by simp [h0]) (by simp [hy])
  have hnorm (t : (ZMod p)ˣ) : ‖ratioTest F y t‖ ^ 2 =
      if t = 1 then 0 else ‖F ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1))‖ ^ 2 := by
    unfold ratioTest
    split_ifs <;> simp
  simp_rw [hnorm]
  rw [hsum]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetTotalMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The total character mass of the cross-pair quartet coefficients -/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.quartetTotalFintype
theorem quartetParameterValue_sum_characters {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : (ZMod p)ˣ) (z t : (ZMod p)ˣ) :
    (∑ ν : MulChar (ZMod p) ℂ, ‖quartetParameterValue g h left right ν y z t‖ ^ 2) =
      (Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ) ^ 2 *
        ∑ d : ZMod p,
          ‖fieldBottomPairValue g d (quartetLeftRatio left z d (d - y))‖ ^ 2 *
          ‖fieldBottomPairValue h (d - y) (quartetRightRatio right t d (d - y))‖ ^ 2 := by
  have hh := ratioDifferenceTransform_parseval
    (fun d => fieldBottomPairValue g d (quartetLeftRatio left z d (d - y)) *
      fieldBottomPairValue h (d - y) (quartetRightRatio right t d (d - y)))
      y (by simp) (by simp)
  simpa only [quartetParameterValue, ratioDifferenceTransform, norm_mul, mul_pow] using hh

theorem fieldPairMoment_parameter_average {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (friendly : Bool) (d e : (ZMod p)ˣ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ,
        ‖fieldBottomPairValue g d (quartetLeftRatio friendly z d e)‖ ^ 2) =
      fieldPairMoment g d := by
  let a := if friendly then d else e⁻¹
  have he (z : (ZMod p)ˣ) : quartetLeftRatio friendly z d e = ((z * a : (ZMod p)ˣ) : ZMod p) := by
    cases friendly
    · change (z : ZMod p) / e = ((z * e⁻¹ : (ZMod p)ˣ) : ZMod p)
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
    · rfl
  simp_rw [he]
  unfold fieldPairMoment
  congr 1
  exact (Equiv.mulRight a).bijective.sum_comp (fun z => ‖fieldBottomPairValue g d z‖ ^ 2)

theorem quartet_pair_parameter_average {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (d e : ZMod p) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ, (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        ∑ t : (ZMod p)ˣ,
          ‖fieldBottomPairValue g d (quartetLeftRatio left z d e)‖ ^ 2 *
          ‖fieldBottomPairValue h e (quartetRightRatio right t d e)‖ ^ 2) =
      fieldPairMoment g d * fieldPairMoment h e := by
  by_cases hd : d = 0
  · simp [hd]
  by_cases he : e = 0
  · simp [he]
  let D : (ZMod p)ˣ := Units.mk0 d hd
  let E : (ZMod p)ˣ := Units.mk0 e he
  have hL := fieldPairMoment_parameter_average g left D E
  have hR := fieldPairMoment_parameter_average h right E D
  change (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ, (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        ∑ t : (ZMod p)ˣ,
          ‖fieldBottomPairValue g D (quartetLeftRatio left z D E)‖ ^ 2 *
          ‖fieldBottomPairValue h E (quartetLeftRatio right t E D)‖ ^ 2) =
      fieldPairMoment g D * fieldPairMoment h E
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [← hL, ← hR]
  ring

theorem quartetParameterMoment_nonneg {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0 ≤ quartetParameterMoment g h left right ν y := by
  unfold quartetParameterMoment
  positivity

/-- The total local mass is exactly a nonnegative difference convolution. -/
theorem sum_quartetParameterMoment {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : (ZMod p)ˣ) :
    (∑ ν : MulChar (ZMod p) ℂ, quartetParameterMoment g h left right ν y) =
      (Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ) ^ 2 *
        differenceMoment (fieldPairMoment g) (fieldPairMoment h) y := by
  let U : ℝ := Fintype.card (ZMod p)ˣ
  let K : ℝ := U / (p : ℝ) ^ 2
  let A (ν : MulChar (ZMod p) ℂ) (z t : (ZMod p)ˣ) :=
    ‖quartetParameterValue g h left right ν y z t‖ ^ 2
  let B (d : ZMod p) (z t : (ZMod p)ˣ) :=
    ‖fieldBottomPairValue g d (quartetLeftRatio left z d (d - y))‖ ^ 2 *
      ‖fieldBottomPairValue h (d - y) (quartetRightRatio right t d (d - y))‖ ^ 2
  change (∑ ν, U⁻¹ * ∑ z, U⁻¹ * ∑ t, A ν z t) = _
  calc
    _ = U⁻¹ * ∑ z, U⁻¹ * ∑ t, ∑ ν, A ν z t := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
    _ = U⁻¹ * ∑ z, U⁻¹ * ∑ t, K * ∑ d, B d z t := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      exact quartetParameterValue_sum_characters g h left right y z t
    _ = K * ∑ d, U⁻¹ * ∑ z, U⁻¹ * ∑ t, B d z t := by
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod p)ˣ))
        (t := (Finset.univ : Finset (ZMod p)))]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      exact quartet_pair_parameter_average g h left right d (d - y)

/-- Uniform bounded total mass, simultaneously for all four friendly/bad choices. -/
theorem quartetParameterMoment_total_mean_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0) (hh : h 0 = 0)
    (heg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (heh : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ)) (left right : Bool) :
    (∑ ν : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ,
      quartetParameterMoment g h left right ν y) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤
        ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  let U : ℝ := Fintype.card (ZMod p)ˣ
  have hU : 0 < U := by dsimp [U]; exact_mod_cast Fintype.card_pos
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hmean := mean_differenceMajorant_le (fieldPairMoment g) (fieldPairMoment h)
    (fieldPairMoment_nonneg g) (fieldPairMoment_nonneg h)
  have hgm := fieldPairMoment_mean_le g hg heg
  have hhm := fieldPairMoment_mean_le h hh heh
  calc
    _ = (U ^ 2 / (p : ℝ) ^ 2) *
        ((∑ y : (ZMod p)ˣ,
          differenceMajorant (fieldPairMoment g) (fieldPairMoment h) y) / U) := by
      simp only [Finset.sum_div]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_div, sum_quartetParameterMoment]
      simp only [differenceMajorant, ← Finset.mul_sum]
      change _ = U ^ 2 / (p : ℝ) ^ 2 * ((U⁻¹ * _) / U)
      field_simp
    _ ≤ (U ^ 2 / (p : ℝ) ^ 2) *
        (((∑ d : ZMod p, fieldPairMoment g d) / U) *
          ((∑ d : ZMod p, fieldPairMoment h d) / U)) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ ≤ (U ^ 2 / (p : ℝ) ^ 2) * (((p : ℝ) / U) ^ 2 * ((p : ℝ) / U) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hgm hhm
        (div_nonneg (Finset.sum_nonneg fun d _ => fieldPairMoment_nonneg h d) hU.le)
        (sq_nonneg _)
    _ = _ := by dsimp [U]; field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CrossPairMajorant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-pullback majorants for the two moving leaves in different pairs -/

namespace Ostmann

open scoped BigOperators

theorem quartetParameterMoment_mean_le_fourier {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, quartetParameterMoment g h left right ν y) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤
        ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) *
          quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) left right ν := by
  have hparse : (p : ℝ)⁻¹ *
      (∑ y : ZMod p, quartetParameterMoment g h left right ν y) =
        quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) left right ν :=
    quartetParameterValue_parseval g h left right ν
  have hsum : (∑ y : (ZMod p)ˣ, quartetParameterMoment g h left right ν y) ≤
      ∑ y : ZMod p, quartetParameterMoment g h left right ν y := by
    apply OAI.sum_le_sum_of_injOn (fun y : (ZMod p)ˣ => (y : ZMod p))
      Units.val_injective.injOn (Finset.subset_univ _)
    · intro _ _
      exact le_rfl
    · intro y _ _
      exact quartetParameterMoment_nonneg g h left right ν y
  apply (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans_eq
  rw [← hparse]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

theorem crossPairMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0 ≤ crossPairMajorant g h left right ρ y :=
  squareCharacterMass_nonneg _ (fun ν => quartetParameterMoment_nonneg g h left right ν y) ρ

attribute [local instance] OAI.Ostmann.crossPairFintype
theorem crossPairMajorant_mean_eq {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, crossPairMajorant g h left right ρ y) /
      (Fintype.card (ZMod p)ˣ : ℝ) =
        squareCharacterMass (fun ν =>
          (∑ y : (ZMod p)ˣ, quartetParameterMoment g h left right ν y) /
            (Fintype.card (ZMod p)ˣ : ℝ)) ρ := by
  unfold crossPairMajorant squareCharacterMass
  rw [Finset.sum_comm, Finset.sum_div]

theorem crossPairMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : ∀ ν : MulChar (ZMod p) ℂ,
      quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) left right ν ≤ δ)
    (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, crossPairMajorant g h left right ρ y) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤
        2 * (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) * δ) := by
  rw [crossPairMajorant_mean_eq]
  apply squareCharacterMass_le_twice _ _ (by positivity)
  intro ν
  exact (quartetParameterMoment_mean_le_fourier g h left right ν).trans
    (mul_le_mul_of_nonneg_left (hsmall ν) (by positivity))

theorem crossPairMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0) (hh : h 0 = 0)
    (heg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (heh : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ)) (left right : Bool) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ,
      crossPairMajorant g h left right ρ y) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤
        ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  simp_rw [crossPairMajorant_mean_eq]
  rw [sum_squareCharacterMass]
  exact quartetParameterMoment_total_mean_le g h hg hh heg heh left right

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquareRatioCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-coordinate coefficients of a fixed-difference quartet -/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.squareRatioFintype
theorem squareCharacterMass_inv {p : ℕ} [Fact p.Prime]
    (a : MulChar (ZMod p) ℂ → ℝ) (ρ : MulChar (ZMod p) ℂ) :
    squareCharacterMass (fun ν => a ν⁻¹) ρ = squareCharacterMass a ρ⁻¹ := by
  classical
  unfold squareCharacterMass
  refine Finset.sum_nbij' (fun ν => ν⁻¹) (fun ν => ν⁻¹) ?_ ?_ ?_ ?_ ?_ <;>
    intros <;> simp_all [Finset.mem_filter, inv_pow]

theorem ratioTest_mellinCoefficient {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (h0 : F 0 = 0) (hy : F y = 0)
    (ν : MulChar (ZMod p) ℂ) :
    mellinCoefficient (ratioTest F y) ν =
      ((p : ℂ) / (Fintype.card (ZMod p)ˣ : ℂ)) *
        ratioDifferenceTransform F y ν⁻¹ := by
  have h := ratioDifferenceTransform_eq_mellin F y h0 hy ν⁻¹
  rw [inv_inv] at h
  rw [h]
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hU : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The square-root ambiguity of a moving leaf costs exactly the square-fiber
factor two. The ratio-to-difference normalization is explicit. -/
theorem ratioTest_square_mellin_bound {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (h0 : F 0 = 0) (hy : F y = 0)
    (K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun z => ratioTest F y (K * z ^ 2)) ρ‖ ^ 2 ≤
      2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        squareCharacterMass (fun ν => ‖ratioDifferenceTransform F y ν‖ ^ 2) ρ⁻¹ := by
  classical
  have h := mellinCoefficient_square_pullback_bound Finset.univ
    (mellinCoefficient (ratioTest F y)) (ratioTest F y)
    (fun z => (mellin_inversion _ z).symm) K ρ
  simp_rw [ratioTest_mellinCoefficient F y h0 hy, norm_mul, norm_div,
    Complex.norm_natCast, mul_pow] at h
  have he : (∑ ν ∈ Finset.univ.filter (fun ν : MulChar (ZMod p) ℂ => ν ^ 2 = ρ),
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        ‖ratioDifferenceTransform F y ν⁻¹‖ ^ 2) =
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        squareCharacterMass (fun ν => ‖ratioDifferenceTransform F y ν‖ ^ 2) ρ⁻¹ := by
    rw [← Finset.mul_sum]
    congr 1
    have hinv := squareCharacterMass_inv (fun ν => ‖ratioDifferenceTransform F y ν‖ ^ 2) ρ
    unfold squareCharacterMass at hinv ⊢
    convert hinv using 2
    ext
    simp
  calc _ ≤ _ := h
    _ = 2 * (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        squareCharacterMass (fun ν => ‖ratioDifferenceTransform F y ν‖ ^ 2) ρ⁻¹) := by
      congr 1
      convert he using 2
      ext
      simp
    _ = _ := by ring

theorem quartetRatioValue_at_difference {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y d e z t : (ZMod p)ˣ)
    (hdiff : (d : ZMod p) - e = y) :
    quartetRatioValue g h left right y z t (d / e) =
      fieldBottomPairValue g d (quartetLeftRatio left z d e) *
        fieldBottomPairValue h e (quartetRightRatio right t d e) := by
  have hde : (d : ZMod p) ≠ e := by
    intro he
    have hz : (y : ZMod p) = 0 := by rw [← hdiff, he, sub_self]
    exact Units.ne_zero y hz
  have ht : d / e ≠ 1 := by
    intro hh
    apply hde
    exact Units.ext_iff.mp (div_eq_one.mp hh)
  have hc := pair_coordinates_reconstruct (d : ZMod p) e (Units.ne_zero e) hde
  have hx : (y : ZMod p) * ((d / e : (ZMod p)ˣ) : ZMod p) /
      (((d / e : (ZMod p)ˣ) : ZMod p) - 1) = d := by
    rw [← hdiff, Units.val_div_eq_div_val]
    exact congrArg Prod.fst hc
  simp only [quartetRatioValue, ratioTest, ht, ite_false, if_false, hx, sub_eq_iff_eq_add.mpr
    (show (d : ZMod p) = (e : ZMod p) + y by linear_combination hdiff)]

theorem quartetRatioValue_square_mellin_bound {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : (ZMod p)ˣ)
    (z t K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun r => quartetRatioValue g h left right y z t (K * r ^ 2)) ρ‖ ^ 2 ≤
      2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        squareCharacterMass (fun ν => ‖quartetParameterValue g h left right ν y z t‖ ^ 2) ρ⁻¹ := by
  exact ratioTest_square_mellin_bound _ y (by simp) (by simp) K ρ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CrossPairHeldAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the two held leaves in a cross-pair quartet -/

namespace Ostmann

open scoped BigOperators

theorem sum_square_coset_pair_le_four {p : ℕ} [Fact p.Prime]
    (K L : (ZMod p)ˣ) (f : (ZMod p)ˣ → (ZMod p)ˣ → ℝ)
    (hf : ∀ z t, 0 ≤ f z t) :
    (∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ, f (K * a ^ 2) (L * b ^ 2)) ≤
      4 * ∑ z : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ, f z t := by
  calc
    _ ≤ ∑ a : (ZMod p)ˣ, 2 * ∑ t : (ZMod p)ˣ, f (K * a ^ 2) t :=
      Finset.sum_le_sum fun a _ => sum_square_coset_le_twice L _ (hf _)
    _ = 2 * ∑ a : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ, f (K * a ^ 2) t := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (2 * ∑ z : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ, f z t) :=
      mul_le_mul_of_nonneg_left
        (sum_square_coset_le_twice K _ (fun z => Finset.sum_nonneg fun t _ => hf z t))
        (by norm_num)
    _ = _ := by ring

noncomputable local instance crossHeldFintype_rfc8d08_1 {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _
theorem crossPairMajorant_parameter_average {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : ZMod p) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ z : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ t : (ZMod p)ˣ,
        squareCharacterMass (fun ν => ‖quartetParameterValue g h left right ν y z t‖ ^ 2) ρ) =
      crossPairMajorant g h left right ρ y := by
  classical
  unfold crossPairMajorant squareCharacterMass quartetParameterMoment
  simp only [Finset.mul_sum]
  exact Eq.trans (Finset.sum_congr rfl fun z _ => Finset.sum_comm) Finset.sum_comm

/-- Both held leaves may have any fixed square-coset multipliers. The moving
coordinate multiplier may depend on both held leaves. -/
theorem crossPair_held_coefficient_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : (ZMod p)ˣ)
    (K L : (ZMod p)ˣ) (M : (ZMod p)ˣ → (ZMod p)ˣ → (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r => quartetRatioValue g h left right y
          (K * a ^ 2) (L * b ^ 2) (M a b * r ^ 2)) ρ‖ ^ 2) ≤
      8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        crossPairMajorant g h left right ρ⁻¹ y := by
  let U : ℝ := Fintype.card (ZMod p)ˣ
  let C : ℝ := 2 * ((p : ℝ) / U) ^ 2
  let f (z t : (ZMod p)ˣ) :=
    squareCharacterMass (fun ν => ‖quartetParameterValue g h left right ν y z t‖ ^ 2) ρ⁻¹
  have hC : 0 ≤ C := by positivity
  have hU : 0 ≤ U⁻¹ := by positivity
  have hf (z t : (ZMod p)ˣ) : 0 ≤ f z t :=
    squareCharacterMass_nonneg _ (fun ν => sq_nonneg _) _
  have hpoint (a b : (ZMod p)ˣ) :
      ‖mellinCoefficient (fun r => quartetRatioValue g h left right y
        (K * a ^ 2) (L * b ^ 2) (M a b * r ^ 2)) ρ‖ ^ 2 ≤ C * f (K * a ^ 2) (L * b ^ 2) :=
    quartetRatioValue_square_mellin_bound g h left right y _ _ _ ρ
  calc
    _ ≤ U⁻¹ * (∑ a : (ZMod p)ˣ, U⁻¹ * ∑ b : (ZMod p)ˣ,
        C * f (K * a ^ 2) (L * b ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hU
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hpoint a b) hU
    _ = U⁻¹ * U⁻¹ * C * (∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ,
        f (K * a ^ 2) (L * b ^ 2)) := by
      simp only [← Finset.mul_sum]
      ring
    _ ≤ U⁻¹ * U⁻¹ * C * (4 * ∑ z : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ, f z t) :=
      mul_le_mul_of_nonneg_left (sum_square_coset_pair_le_four K L f hf)
        (mul_nonneg (mul_nonneg hU hU) hC)
    _ = 8 * ((p : ℝ) / U) ^ 2 *
        (U⁻¹ * ∑ z : (ZMod p)ˣ, U⁻¹ * ∑ t : (ZMod p)ˣ, f z t) := by
      simp only [← Finset.mul_sum, C]
      ring
    _ = _ := by rw [crossPairMajorant_parameter_average]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeLeafProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf-product fibers in a full binary tree -/

namespace Ostmann

open scoped BigOperators

theorem card_treeLeafTuple {U : Type*} [Fintype U] (n : ℕ) :
    Fintype.card (TreeLeafTuple U n) = Fintype.card U ^ (2 ^ n) := by
  induction n with
  | zero =>
    change Fintype.card U = Fintype.card U ^ (2 ^ 0)
    simp
  | succ n ih =>
    change Fintype.card (TreeLeafTuple U n × TreeLeafTuple U n) = _
    rw [Fintype.card_prod, ih, pow_succ (2 : ℕ), pow_mul, pow_two]

theorem card_treeLeafFiber {U : Type*} [CommGroup U] [Fintype U] (n : ℕ) (P : U) :
    Fintype.card (TreeLeafFiber U n P) = Fintype.card U ^ (2 ^ n - 1) := by
  induction n generalizing P with
  | zero => rw [Fintype.card_congr (treeLeafFiberZeroEquiv P)]; simp
  | succ n ih =>
    rw [Fintype.card_congr (treeLeafFiberSuccEquiv n P), Fintype.card_sigma]
    simp only [Fintype.card_prod, ih, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.cast_id]
    rw [← pow_add, ← pow_succ']
    congr 1
    have h : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    rw [pow_succ]
    omega

theorem sum_treeLeafFiber_succ {U R : Type*} [CommGroup U] [Fintype U]
    [AddCommMonoid R] (n : ℕ) (P : U) (f : TreeLeafTuple U (n + 1) → R) :
    (∑ x : TreeLeafFiber U (n + 1) P, f x.1) =
      ∑ m : U, ∑ a : TreeLeafFiber U n m, ∑ b : TreeLeafFiber U n (P / m),
        f (a.1, b.1) := by
  have h := (treeLeafFiberSuccEquiv n P).symm.sum_comp (fun x => f x.1)
  change (∑ x : (Σ m : U, TreeLeafFiber U n m × TreeLeafFiber U n (P / m)),
    f (x.2.1.1, x.2.2.1)) = _ at h
  simpa only [Fintype.sum_sigma, Fintype.sum_prod_type] using h.symm

theorem sum_treeLeafTuple_by_product {U R : Type*} [CommGroup U] [Fintype U]
    [AddCommMonoid R] (n : ℕ) (f : TreeLeafTuple U n → R) :
    (∑ x : TreeLeafTuple U n, f x) = ∑ P : U, ∑ x : TreeLeafFiber U n P, f x.1 := by
  classical
  have h := (Equiv.sigmaFiberEquiv (treeLeafProduct (U := U) n)).sum_comp f
  change (∑ x : (Σ P : U, TreeLeafFiber U n P), f x.2.1) = _ at h
  simpa only [Fintype.sum_sigma] using h.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational coordinates at a tree split

These identities are equations `tree-difference-ratio`, `tree-held-square`,
and `tree-p-square` of the manuscript. Nonzero hypotheses state precisely
that the reconstructed node is valid.
-/

namespace Ostmann

theorem reconstructedEntry_relation {K : Type*} [Field K]
    (s sL sR u HL HR : K) (hs : s ≠ 0) (hu : u ≠ 0) :
    reconstructedEntry s sL sR u HL HR * (s * u) = sL * HR - sR * HL := by
  exact div_mul_cancel₀ _ (mul_ne_zero hs hu)

theorem tree_child_difference {K : Type*} [Field K]
    (s sL sR D u HL HR P : K)
    (hD : D ≠ 0) (hu : u ≠ 0) (hL : HL ≠ 0) (hR : HR ≠ 0) (hP : P ≠ 0)
    (hrel : P * (s * u) = sL * HR - sR * HL) :
    childArgument sL D u HL P - childArgument sR D u HR P = parentArgument s D HL HR := by
  unfold childArgument parentArgument
  field_simp
  linear_combination -hrel

theorem tree_child_ratio {K : Type*} [Field K]
    (sL sR D u HL HR P : K)
    (hsR : sR ≠ 0) (hD : D ≠ 0) (hu : u ≠ 0)
    (hL : HL ≠ 0) (hR : HR ≠ 0) (hP : P ≠ 0) :
    childArgument sL D u HL P / childArgument sR D u HR P = (sL / sR) * (HR / HL) := by
  unfold childArgument
  field_simp

/-- Exposing a child product makes its ratio an inverse square of the free product. -/
theorem tree_product_ratio {G : Type*} [CommGroup G]
    (sL sR XL XR CL CR P m : G) :
    (sL / sR) * ((XR * CR * (P / m)) / (XL * CL * m)) =
      ((sL / sR) * (XR * CR * P / (XL * CL))) * (m⁻¹) ^ 2 := by
  simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]

/-- Difference and ratio identify the child arguments with the sampling coordinates. -/
theorem children_eq_pair_coordinates {K : Type*} [Field K]
    (x z d t : K) (hz : z ≠ 0) (hd : d ≠ 0)
    (hdiff : x - z = d) (hratio : x / z = t) :
    (x, z) = (d * t / (t - 1), d / (t - 1)) := by
  have hxz : x ≠ z := by intro h; apply hd; rw [← hdiff, h, sub_self]
  rw [← hdiff, ← hratio]
  exact (pair_coordinates_reconstruct x z hz hxz).symm

/-- The rational tree formulas produce exactly the pair used by the density model. -/
theorem tree_children_eq_pair_coordinates {K : Type*} [Field K]
    (s sL sR D u HL HR P : K)
    (hs : s ≠ 0) (hsR : sR ≠ 0) (hD : D ≠ 0) (hu : u ≠ 0)
    (hL : HL ≠ 0) (hR : HR ≠ 0) (hP : P ≠ 0)
    (hrel : P * (s * u) = sL * HR - sR * HL) :
    (childArgument sL D u HL P, childArgument sR D u HR P) =
      (parentArgument s D HL HR * ((sL / sR) * (HR / HL)) /
        ((sL / sR) * (HR / HL) - 1),
       parentArgument s D HL HR / ((sL / sR) * (HR / HL) - 1)) := by
  apply children_eq_pair_coordinates
  · exact div_ne_zero hsR (by simp only [ne_eq, mul_eq_zero, hD, hP, hu, hR, or_self, not_false_eq_true])
  · exact div_ne_zero hs (mul_ne_zero (mul_ne_zero hD hL) hR)
  · exact tree_child_difference s sL sR D u HL HR P hD hu hL hR hP hrel
  · exact tree_child_ratio sL sR D u HL HR P hsR hD hu hL hR hP

/-- A reconstructed node is invalid precisely at the singular child ratio. -/
theorem reconstructedEntry_zero_iff_ratio_one {K : Type*} [Field K]
    (s sL sR u HL HR : K) (hs : s ≠ 0) (hsR : sR ≠ 0)
    (hu : u ≠ 0) (hL : HL ≠ 0) :
    reconstructedEntry s sL sR u HL HR = 0 ↔ (sL / sR) * (HR / HL) = 1 := by
  have hden : sR * HL ≠ 0 := mul_ne_zero hsR hL
  have heq : (sL / sR) * (HR / HL) = (sL * HR) / (sR * HL) := by ring
  rw [heq, div_eq_one_iff_eq hden]
  unfold reconstructedEntry
  rw [div_eq_zero_iff, or_iff_left (mul_ne_zero hs hu), sub_eq_zero]

/-- At a fixed node product the root argument is independent of the free split. -/
theorem tree_parent_fixed_product {K : Type*} [Field K]
    (s D XL XR CL CR P m : K) (hm : m ≠ 0) :
    parentArgument s D (XL * CL * m) (XR * CR * (P / m)) =
      s / (D * XL * CL * XR * CR * P) := by
  unfold parentArgument
  congr 1
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RationalNodeDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The density bound for an actual reconstructed node

The fixed parent product makes its argument independent of the split.
The reconstructed entry vanishes exactly when the child ratio is one.
Thus the inverse-square density estimate applies to the actual formulas,
with the manuscript's invalid-node convention.
-/

namespace Ostmann

open scoped BigOperators

theorem rationalNodeValue_eq_ratio {p : ℕ} [Fact p.Prime]
    (s sL sR D u XL XR CL CR P : (ZMod p)ˣ)
    (f g : ZMod p → ℝ) (m : (ZMod p)ˣ) :
    rationalNodeValue s sL sR D u XL XR CL CR P f g m =
      let d := rationalNodeArgument s D XL XR CL CR P
      let t := rationalNodeRatioConstant sL sR XL XR CL CR P * (m⁻¹) ^ 2
      if t = 1 then 0 else
        f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
          g ((d : ZMod p) / ((t : ZMod p) - 1)) := by
  classical
  let HL : (ZMod p)ˣ := XL * CL * m
  let HR : (ZMod p)ˣ := XR * CR * (P / m)
  let v := reconstructedEntry (s : ZMod p) sL sR u HL HR
  let d := rationalNodeArgument s D XL XR CL CR P
  let t := rationalNodeRatioConstant sL sR XL XR CL CR P * (m⁻¹) ^ 2
  have ht : (sL : ZMod p) / sR * ((HR : ZMod p) / HL) = (t : ZMod p) := by
    have h : (sL / sR) * (HR / HL) = t :=
      tree_product_ratio sL sR XL XR CL CR P m
    exact_mod_cast h
  have hd : parentArgument (s : ZMod p) D HL HR = (d : ZMod p) := by
    dsimp [HL, HR, d, rationalNodeArgument]
    simp only [Units.val_mul, Units.val_div_eq_div_val]
    exact tree_parent_fixed_product (s : ZMod p) D XL XR CL CR P m (Units.ne_zero m)
  have hv : v = 0 ↔ t = 1 := by
    have h := reconstructedEntry_zero_iff_ratio_one (s : ZMod p) sL sR u HL HR
      (Units.ne_zero s) (Units.ne_zero sR) (Units.ne_zero u) (Units.ne_zero HL)
    rw [ht] at h
    constructor
    · intro hz
      exact Units.ext (h.mp hz)
    · intro h1
      apply h.mpr
      simp only [h1, Units.val_one]
  change (if v = 0 then 0 else
    f (childArgument sL D u HL v) * g (childArgument sR D u HR v)) =
      if t = 1 then 0 else
        f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
          g ((d : ZMod p) / ((t : ZMod p) - 1))
  by_cases hv0 : v = 0
  · simp only [hv0, hv.mp hv0, ite_true, if_true]
  · have ht1 : t ≠ 1 := fun h => hv0 (hv.mpr h)
    simp only [hv0, ht1, ite_false, if_false]
    have hpair := tree_children_eq_pair_coordinates (s : ZMod p) sL sR D u HL HR v
      (Units.ne_zero s) (Units.ne_zero sR) (Units.ne_zero D) (Units.ne_zero u)
      (Units.ne_zero HL) (Units.ne_zero HR) hv0
      (reconstructedEntry_relation (s : ZMod p) sL sR u HL HR (Units.ne_zero s) (Units.ne_zero u))
    rw [ht, hd] at hpair
    exact congrArg (fun xz : ZMod p × ZMod p => f xz.1 * g xz.2) hpair

/-- Conditional counting density of one actual rational tree split. -/
theorem rationalNodeValue_sum_le {p : ℕ} [Fact p.Prime]
    (s sL sR D u XL XR CL CR P : (ZMod p)ˣ)
    (f g : ZMod p → ℝ) (hf : f 0 = 0) (hg : g 0 = 0)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (∑ m : (ZMod p)ˣ, rationalNodeValue s sL sR D u XL XR CL CR P f g m) ≤
      2 * ∑ x : ZMod p, f x * g (x - rationalNodeArgument s D XL XR CL CR P) := by
  simp_rw [rationalNodeValue_eq_ratio]
  exact pair_inverse_square_density _ _ f g hf hg hfn hgn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recursive rational tree data

The product coefficient is an index of the data type. At every split,
its child indices encode exactly the consistency conditions on the
fixed constants in `src36`.
-/

namespace Ostmann

open scoped BigOperators

theorem rationalTreeArgument_child {p : ℕ} [Fact p.Prime]
    (s D u X C m v : (ZMod p)ˣ) :
    (rationalTreeArgument s (u * C) D v X m : ZMod p) =
      childArgument (s : ZMod p) D u ((X * C * m : (ZMod p)ˣ) : ZMod p) v := by
  simp only [rationalTreeArgument, childArgument, Units.val_div_eq_div_val, Units.val_mul]
  congr 1
  ring

theorem rationalTreeArgument_node {p : ℕ} [Fact p.Prime]
    (s CL CR D XL XR P : (ZMod p)ˣ) :
    rationalTreeArgument s (CL * CR) D XL XR P = rationalNodeArgument s D XL XR CL CR P := by
  unfold rationalTreeArgument rationalNodeArgument
  congr 1
  simp only [mul_left_comm, mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalPairValue
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact bottom-pair identification in a reconstructed rational tree -/

namespace Ostmann

open scoped ComplexConjugate

/-- A bottom node with the usual alternating conjugation is exactly the pair
function used in the Fourier and Mellin estimates, including invalid nodes. -/
theorem rationalTreeAmplitude_pair {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D s sL sR CL CR u XL XR mL mR : (ZMod p)ˣ) :
    rationalTreeAmplitude g D
      (.node s CL CR u (.leaf sL (u * CL)) (.leaf sR (u * CR)))
      XL XR (false, true) (mL, mR) =
      fieldBottomPairValue g
        (rationalTreeArgument s (CL * CR) D XL XR (mL * mR))
        (((sL / sR) * ((XR * CR * mR) / (XL * CL * mL)) : (ZMod p)ˣ) : ZMod p) := by
  let HL := XL * CL * mL
  let HR := XR * CR * mR
  let v := reconstructedEntry (s : ZMod p) sL sR u HL HR
  let d := rationalTreeArgument s (CL * CR) D XL XR (mL * mR)
  let t := (sL / sR) * (HR / HL)
  have hdiff : parentArgument (s : ZMod p) D HL HR = (d : ZMod p) := by
    simp only [parentArgument, d, rationalTreeArgument, HL, HR,
      Units.val_div_eq_div_val, Units.val_mul]
    congr 1
    ring
  have ht : ((sL : ZMod p) / sR) * ((HR : ZMod p) / HL) = (t : ZMod p) := by
    simp only [t, Units.val_mul, Units.val_div_eq_div_val]
  have hzero : v = 0 ↔ t = 1 := by
    have hz := reconstructedEntry_zero_iff_ratio_one (s : ZMod p) sL sR u HL HR
      (Units.ne_zero s) (Units.ne_zero sR) (Units.ne_zero u) (Units.ne_zero HL)
    rw [ht] at hz
    constructor
    · intro h
      exact Units.ext (hz.mp h)
    · intro h
      exact hz.mpr (congrArg (fun a : (ZMod p)ˣ => (a : ZMod p)) h)
  change (if hv : v = 0 then 0 else
    g (rationalTreeArgument sL (u * CL) D (Units.mk0 v hv) XL mL) *
      star (g (rationalTreeArgument sR (u * CR) D (Units.mk0 v hv) XR mR))) =
    fieldBottomPairValue g d t
  rw [fieldBottomPairValue_units]
  by_cases hv : v = 0
  · simp [hv, bottomPairValue, hzero.mp hv]
  · have ht1 : t ≠ 1 := fun h => hv (hzero.mpr h)
    simp only [hv, dite_false, bottomPairValue, ht1, ite_false, if_false]
    let V : (ZMod p)ˣ := Units.mk0 v hv
    have hc := tree_children_eq_pair_coordinates (s : ZMod p) sL sR D u HL HR V
      (Units.ne_zero s) (Units.ne_zero sR) (Units.ne_zero D) (Units.ne_zero u)
      (Units.ne_zero HL) (Units.ne_zero HR) (Units.ne_zero V)
      (reconstructedEntry_relation (s : ZMod p) sL sR u HL HR
        (Units.ne_zero s) (Units.ne_zero u))
    rw [hdiff, ht] at hc
    have hL : (rationalTreeArgument sL (u * CL) D V XL mL : ZMod p) =
        (d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1) := by
      rw [rationalTreeArgument_child]
      exact congrArg Prod.fst hc
    have hR : (rationalTreeArgument sR (u * CR) D V XR mR : ZMod p) =
        (d : ZMod p) / ((t : ZMod p) - 1) := by
      rw [rationalTreeArgument_child]
      exact congrArg Prod.snd hc
    change g (rationalTreeArgument sL (u * CL) D V XL mL) *
      star (g (rationalTreeArgument sR (u * CR) D V XR mR)) = _
    rw [hL, hR]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetFriendlyCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-friendly orientation of an actual rational quartet -/

namespace Ostmann

open scoped BigOperators

theorem pair_ratio_friendly {p : ℕ} [Fact p.Prime]
    (D s s₁ s₂ C₁ C₂ V X m₁ m₂ : (ZMod p)ˣ) :
    (s₁ / s₂) * ((X * C₂ * m₂) / (V * C₁ * m₁)) =
      ((D * s₁ / (s₂ * s)) * (X * C₂) ^ 2 * m₂ ^ 2) *
        rationalTreeArgument s (C₁ * C₂) D V X (m₁ * m₂) := by
  unfold rationalTreeArgument
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  field_simp

/-- The ratio at the quartet root is a fixed multiple of the moving square. -/
theorem quartet_friendly_ratio {p : ℕ} [Fact p.Prime]
    (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a b r : (ZMod p)ˣ) :
    (Q.sL / Q.sR) * ((XR * Q.CR * (P * r / (a * b) * b)) /
      (XL * Q.CL * (r⁻¹ * a))) = quartetMovingMultiplier Q XL XR P a * r ^ 2 := by
  unfold quartetMovingMultiplier
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val]
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairOrientationValue
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversing the free and held leaves of a bottom pair -/

namespace Ostmann

open scoped ComplexConjugate

theorem fieldBottomPairValue_formula {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) (hd : d ≠ 0) (ht : t ≠ 0) :
    fieldBottomPairValue g d t = if t = 1 then 0 else
      g (d * t / (t - 1)) * conj (g (d / (t - 1))) := by
  have hi : (Units.mk0 t ht : (ZMod p)ˣ) = 1 ↔ t = 1 := by
    constructor
    · exact fun h => congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    · exact fun h => Units.ext h
  simp only [fieldBottomPairValue, hd, ht, dite_false, bottomPairValue, hi, Units.val_mk0]

/-- Reversing a pair negates its difference, inverts its ratio and conjugates
its base function. The two leaf factors themselves remain unchanged. -/
theorem fieldBottomPairValue_reverse {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) :
    fieldBottomPairValue (fun x => conj (g x)) (-d) t⁻¹ = fieldBottomPairValue g d t := by
  by_cases hd : d = 0
  · simp [hd]
  by_cases ht : t = 0
  · simp [ht]
  rw [fieldBottomPairValue_formula _ _ _ (neg_ne_zero.mpr hd) (inv_ne_zero ht),
    fieldBottomPairValue_formula g d t hd ht]
  by_cases ht1 : t = 1
  · simp [ht1]
  have hi1 : t⁻¹ ≠ 1 := by
    intro h
    apply ht1
    simpa only [inv_inv, inv_one] using congrArg (fun x : ZMod p => x⁻¹) h
  simp only [ht1, hi1, ite_false, if_false, starRingEnd_apply, star_star]
  have hden : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have ha : -d * t⁻¹ / (t⁻¹ - 1) = d / (t - 1) := by field_simp; ring
  have hb : -d / (t⁻¹ - 1) = d * t / (t - 1) := by field_simp; ring
  rw [ha, hb]
  exact mul_comm _ _

theorem fieldBottomPairValue_negate {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) :
    fieldBottomPairValue (fun x => g (-x)) d t = fieldBottomPairValue g (-d) t := by
  by_cases hd : d = 0
  · simp [hd]
  by_cases ht : t = 0
  · simp [ht]
  rw [fieldBottomPairValue_formula _ _ _ hd ht,
    fieldBottomPairValue_formula _ _ _ (neg_ne_zero.mpr hd) ht]
  split_ifs
  · rfl
  · simp only [neg_mul, neg_div]

/-- Reversing the pair while keeping its difference positive reflects and
conjugates the base function. -/
theorem fieldBottomPairValue_reflect_reverse {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : ZMod p) :
    fieldBottomPairValue (fun x => conj (g (-x))) d t⁻¹ = fieldBottomPairValue g d t := by
  rw [fieldBottomPairValue_negate (fun x => conj (g x)), fieldBottomPairValue_reverse]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetBadCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Shared-entry square cancellation in the bad quartet orientations -/

namespace Ostmann

/-- The inverse ratio uses the square of the first, now held, entry. -/
theorem pair_inverse_ratio_held {p : ℕ} [Fact p.Prime]
    (D s s₁ s₂ C₁ C₂ V X m₁ m₂ : (ZMod p)ˣ) :
    ((s₁ / s₂) * ((X * C₂ * m₂) / (V * C₁ * m₁)))⁻¹ =
      ((D * s₂ / (s₁ * s)) * (V * C₁) ^ 2 * m₁ ^ 2) *
        rationalTreeArgument s (C₁ * C₂) D V X (m₁ * m₂) := by
  unfold rationalTreeArgument
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val]
  field_simp

/-- The common reconstructed entry has the exact square needed to cancel
one difference from each child pair. The child products need only agree. -/
theorem rationalQuartet_shared_square {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (V XL XR M N : (ZMod p)ˣ) :
    V ^ 2 = (Q.sL * Q.sR / (Q.s * D * Q.u ^ 2)) *
      rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR (M * N) /
        (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL M *
          rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR N) := by
  unfold rationalTreeArgument
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  field_simp

/-- Algebraic cancellation producing `lambda / e` in the bad orientation. -/
theorem bad_ratio_of_shared_square {p : ℕ} [Fact p.Prime]
    (K C y V d e m : (ZMod p)ˣ) (hV : V ^ 2 = C * y / (d * e)) :
    (K * (V * m) ^ 2) * d = (K * C * y) * m ^ 2 / e := by
  rw [mul_pow, hV]
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  field_simp

/-- The corresponding cancellation on the right produces `lambda / d`. -/
theorem bad_ratio_of_shared_square_right {p : ℕ} [Fact p.Prime]
    (K C y V d e m : (ZMod p)ˣ) (hV : V ^ 2 = C * y / (d * e)) :
    (K * (V * m) ^ 2) * e = (K * C * y) * m ^ 2 / d := by
  apply bad_ratio_of_shared_square K C y V e d m
  simpa only [mul_comm] using hV

/-- Holding the reconstructed entry on the left gives exactly the bad ratio. -/
theorem rationalQuartet_left_bad_ratio {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (V XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) :
    ((Q.s₁ / Q.s₂) * ((XL * Q.C₂ * m₂) / (V * Q.C₁ * m₁)))⁻¹ =
      (quartetLeftBadHeld D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) * m₁ ^ 2) /
        rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄) := by
  rw [pair_inverse_ratio_held D Q.sL Q.s₁ Q.s₂ Q.C₁ Q.C₂ V XL m₁ m₂]
  rw [Q.left_product]
  have hreshape :
      ((D * Q.s₂ / (Q.s₁ * Q.sL)) * (V * Q.C₁) ^ 2 * m₁ ^ 2) =
        (D * Q.s₂ / (Q.s₁ * Q.sL) * Q.C₁ ^ 2) * (V * m₁) ^ 2 := by
    simp only [mul_pow, mul_assoc, mul_left_comm, mul_comm]
  rw [hreshape]
  exact bad_ratio_of_shared_square _ (quartetSharedConstant D Q) _ V _ _ m₁
    (rationalQuartet_shared_square D Q V XL XR (m₁ * m₂) (m₃ * m₄))

/-- The right held reconstructed entry gives the other bad ratio. -/
theorem rationalQuartet_right_bad_ratio {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (V XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) :
    ((Q.s₃ / Q.s₄) * ((XR * Q.C₄ * m₄) / (V * Q.C₃ * m₃)))⁻¹ =
      (quartetRightBadHeld D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) * m₃ ^ 2) /
        rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂) := by
  rw [pair_inverse_ratio_held D Q.sR Q.s₃ Q.s₄ Q.C₃ Q.C₄ V XR m₃ m₄]
  rw [Q.right_product]
  have hreshape :
      ((D * Q.s₄ / (Q.s₃ * Q.sR)) * (V * Q.C₃) ^ 2 * m₃ ^ 2) =
        (D * Q.s₄ / (Q.s₃ * Q.sR) * Q.C₃ ^ 2) * (V * m₃) ^ 2 := by
    simp only [mul_pow, mul_assoc, mul_left_comm, mul_comm]
  rw [hreshape]
  exact bad_ratio_of_shared_square_right _ (quartetSharedConstant D Q) _ V _ _ m₃
    (rationalQuartet_shared_square D Q V XL XR (m₁ * m₂) (m₃ * m₄))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetOrientedValue
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All free/held orientations in the local quartet value -/

namespace Ostmann

open scoped ComplexConjugate

/-- Both choices on the left use the same child difference and exactly the
friendly/bad parameter table of the Fourier calculation. -/
theorem quartet_left_oriented_value {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (V XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) (friendly : Bool) :
    fieldBottomPairValue g (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
      (((Q.s₁ / Q.s₂) * ((XL * Q.C₂ * m₂) / (V * Q.C₁ * m₁)) : (ZMod p)ˣ) : ZMod p) =
    fieldBottomPairValue (orientedPairBase g friendly)
      (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
      (quartetLeftRatio friendly
        (quartetLeftParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) friendly m₁ m₂)
        (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
        (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))) := by
  cases friendly
  · simp only [orientedPairBase, quartetLeftParameter, quartetLeftRatio, Bool.false_eq_true, ite_false, if_false]
    rw [← fieldBottomPairValue_reflect_reverse g]
    congr 1
    rw [← Units.val_inv_eq_inv_val, ← Units.val_div_eq_div_val]
    exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p))
      (rationalQuartet_left_bad_ratio D Q V XL XR m₁ m₂ m₃ m₄)
  · simp only [orientedPairBase, quartetLeftParameter, quartetLeftRatio, ite_true, if_true]
    have h := pair_ratio_friendly D Q.sL Q.s₁ Q.s₂ Q.C₁ Q.C₂ V XL m₁ m₂
    rw [Q.left_product] at h
    congr 1
    rw [← Units.val_mul]
    exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) h

theorem quartet_right_oriented_value {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (V XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) (friendly : Bool) :
    fieldBottomPairValue g (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))
      (((Q.s₃ / Q.s₄) * ((XR * Q.C₄ * m₄) / (V * Q.C₃ * m₃)) : (ZMod p)ˣ) : ZMod p) =
    fieldBottomPairValue (orientedPairBase g friendly)
      (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))
      (quartetRightRatio friendly
        (quartetRightParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) friendly m₃ m₄)
        (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂))
        (rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄))) := by
  cases friendly
  · simp only [orientedPairBase, quartetRightParameter, quartetRightRatio, Bool.false_eq_true, ite_false, if_false]
    rw [← fieldBottomPairValue_reflect_reverse g]
    congr 1
    rw [← Units.val_inv_eq_inv_val, ← Units.val_div_eq_div_val]
    exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p))
      (rationalQuartet_right_bad_ratio D Q V XL XR m₁ m₂ m₃ m₄)
  · simp only [orientedPairBase, quartetRightParameter, quartetRightRatio, ite_true, if_true]
    have h := pair_ratio_friendly D Q.sR Q.s₃ Q.s₄ Q.C₃ Q.C₄ V XR m₃ m₄
    rw [Q.right_product] at h
    congr 1
    rw [← Units.val_mul]
    exact congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetConjugation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent opposite conjugations on the two bottom sibling pairs -/

namespace Ostmann

open scoped ComplexConjugate

theorem rationalTreeAmplitude_pair_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D s sL sR CL CR u XL XR mL mR : (ZMod p)ˣ) (c : Bool) :
    rationalTreeAmplitude g D
      (.node s CL CR u (.leaf sL (u * CL)) (.leaf sR (u * CR)))
      XL XR (c, !c) (mL, mR) =
      fieldBottomPairValue (pairConjugate g c)
        (rationalTreeArgument s (CL * CR) D XL XR (mL * mR))
        (((sL / sR) * ((XR * CR * mR) / (XL * CL * mL)) : (ZMod p)ˣ) : ZMod p) := by
  cases c
  · exact rationalTreeAmplitude_pair g D s sL sR CL CR u XL XR mL mR
  · have h := rationalTreeAmplitude_pair (fun x => conj (g x)) D s sL sR CL CR u XL XR mL mR
    simp only [pairConjugate, ite_true, if_true, Bool.not_true]
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp [rationalTreeAmplitude]

/-- Both opposite-conjugation choices in each sibling pair are identified
with the actual diagram, independently of the choices in the other pair. -/
theorem rationalTreeAmplitude_quartet_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) (cL cR : Bool) :
    rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
      ((m₁, m₂), (m₃, m₄)) =
      rationalQuartetPairsValue (pairConjugate g cL) (pairConjugate g cR)
        D Q XL XR m₁ m₂ m₃ m₄ := by
  unfold RationalQuartetData.tree
  simp only [rationalTreeAmplitude]
  simp only [rationalTreeFrequency_cast]
  simp only [RationalTreeData.frequency, treeLeafProduct]
  unfold rationalQuartetPairsValue
  dsimp only
  by_cases hv : reconstructedEntry (Q.s : ZMod p) Q.sL Q.sR Q.u
      ((XL * Q.CL * (m₁ * m₂) : (ZMod p)ˣ) : ZMod p)
      ((XR * Q.CR * (m₃ * m₄) : (ZMod p)ˣ) : ZMod p) = 0
  · simp only [hv, dite_true]
  · simp only [hv, dite_false]
    let V : (ZMod p)ˣ := Units.mk0 _ hv
    have hL := rationalTreeAmplitude_cast g D Q.left_product
      (.node Q.sL Q.C₁ Q.C₂ Q.uL (.leaf Q.s₁ (Q.uL * Q.C₁))
        (.leaf Q.s₂ (Q.uL * Q.C₂))) V XL (cL, !cL) (m₁, m₂)
    have hR := rationalTreeAmplitude_cast g D Q.right_product
      (.node Q.sR Q.C₃ Q.C₄ Q.uR (.leaf Q.s₃ (Q.uR * Q.C₃))
        (.leaf Q.s₄ (Q.uR * Q.C₄))) V XR (cR, !cR) (m₃, m₄)
    change rationalTreeAmplitude g D (n := 1) _ V XL (cL, !cL) (m₁, m₂) *
      rationalTreeAmplitude g D (n := 1) _ V XR (cR, !cR) (m₃, m₄) = _
    rw [hL, hR, rationalTreeAmplitude_pair_conjugation, rationalTreeAmplitude_pair_conjugation]
    have hargL := congrArg
      (fun C => (rationalTreeArgument Q.sL C D V XL (m₁ * m₂) : ZMod p)) Q.left_product
    have hargR := congrArg
      (fun C => (rationalTreeArgument Q.sR C D V XR (m₃ * m₄) : ZMod p)) Q.right_product
    rw [hargL, hargR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedQuartetCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quartet ratio coordinates with independent tests in the sibling pairs -/

namespace Ostmann

theorem rationalQuartetPairsValue_oriented {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) (left right : Bool) :
    rationalQuartetPairsValue g h D Q XL XR m₁ m₂ m₃ m₄ =
      quartetRatioValue (orientedPairBase g left) (orientedPairBase h right) left right
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR ((m₁ * m₂) * (m₃ * m₄)))
        (quartetLeftParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) left m₁ m₂)
        (quartetRightParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) right m₃ m₄)
        ((Q.sL / Q.sR) * ((XR * Q.CR * (m₃ * m₄)) / (XL * Q.CL * (m₁ * m₂)))) := by
  let HL := XL * Q.CL * (m₁ * m₂)
  let HR := XR * Q.CR * (m₃ * m₄)
  let v := reconstructedEntry (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
  let y := rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR ((m₁ * m₂) * (m₃ * m₄))
  let t := (Q.sL / Q.sR) * (HR / HL)
  have ht : ((Q.sL : ZMod p) / Q.sR) * ((HR : ZMod p) / HL) = (t : ZMod p) := by
    simp only [t, Units.val_mul, Units.val_div_eq_div_val]
  have hparent : parentArgument (Q.s : ZMod p) D HL HR = (y : ZMod p) := by
    simp only [parentArgument, y, rationalTreeArgument, HL, HR,
      Units.val_div_eq_div_val, Units.val_mul]
    congr 1
    ring
  have hzero : v = 0 ↔ t = 1 := by
    have hz := reconstructedEntry_zero_iff_ratio_one (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
      (Units.ne_zero Q.s) (Units.ne_zero Q.sR) (Units.ne_zero Q.u) (Units.ne_zero HL)
    rw [ht] at hz
    exact ⟨fun h => Units.ext (hz.mp h),
      fun h => hz.mpr (congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) h)⟩
  change (if hv : v = 0 then 0 else _) =
    quartetRatioValue (orientedPairBase g left) (orientedPairBase h right) left right y _ _ t
  by_cases hv : v = 0
  · simp [hv, quartetRatioValue, ratioTest, hzero.mp hv]
  · simp only [hv, dite_false]
    let V : (ZMod p)ˣ := Units.mk0 v hv
    let d := rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂)
    let e := rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄)
    have hdiff : (d : ZMod p) - e = y := by
      dsimp [d, e]
      rw [rationalTreeArgument_child, rationalTreeArgument_child]
      rw [tree_child_difference (Q.s : ZMod p) Q.sL Q.sR D Q.u HL HR V
        (Units.ne_zero D) (Units.ne_zero Q.u) (Units.ne_zero HL) (Units.ne_zero HR)
        (Units.ne_zero V) (reconstructedEntry_relation (Q.s : ZMod p) Q.sL Q.sR Q.u HL HR
          (Units.ne_zero Q.s) (Units.ne_zero Q.u))]
      exact hparent
    have hde : d / e = t := by
      apply Units.ext
      rw [Units.val_div_eq_div_val]
      dsimp [d, e]
      rw [rationalTreeArgument_child, rationalTreeArgument_child]
      exact (tree_child_ratio (Q.sL : ZMod p) Q.sR D Q.u HL HR V
        (Units.ne_zero Q.sR) (Units.ne_zero D) (Units.ne_zero Q.u) (Units.ne_zero HL)
        (Units.ne_zero HR) (Units.ne_zero V)).trans ht
    change fieldBottomPairValue g d _ * fieldBottomPairValue h e _ = _
    rw [quartet_left_oriented_value g D Q V XL XR m₁ m₂ m₃ m₄ left,
      quartet_right_oriented_value h D Q V XL XR m₁ m₂ m₃ m₄ right]
    have h := quartetRatioValue_at_difference (orientedPairBase g left) (orientedPairBase h right)
      left right y d e
      (quartetLeftParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) left m₁ m₂)
      (quartetRightParameter D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) right m₃ m₄) hdiff
    rw [hde] at h
    exact h.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetCrossBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient bound for every cross-pair orientation of an actual quartet -/

namespace Ostmann

open scoped BigOperators

theorem crossLeftLeaves_product {U : Type*} [CommGroup U]
    (friendly : Bool) (a r : U) :
    (crossLeftLeaves friendly a r).1 * (crossLeftLeaves friendly a r).2 = r⁻¹ * a := by
  cases friendly <;> simp [crossLeftLeaves, mul_comm]

theorem crossRightLeaves_product {U : Type*} [CommGroup U]
    (friendly : Bool) (P a b r : U) :
    (crossRightLeaves friendly P a b r).1 * (crossRightLeaves friendly P a b r).2 =
      P * r / (a * b) * b := by
  cases friendly <;> simp [crossRightLeaves, mul_comm]

theorem crossLeftLeaves_parameter {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a r : (ZMod p)ˣ)
    (friendly : Bool) :
    quartetLeftParameter D Q XL XR P friendly
      (crossLeftLeaves friendly a r).1 (crossLeftLeaves friendly a r).2 =
      (if friendly then quartetLeftHeld D Q XL else quartetLeftBadHeld D Q XL XR P) * a ^ 2 := by
  cases friendly <;> rfl

theorem crossRightLeaves_parameter {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a b r : (ZMod p)ˣ)
    (friendly : Bool) :
    quartetRightParameter D Q XL XR P friendly
      (crossRightLeaves friendly P a b r).1 (crossRightLeaves friendly P a b r).2 =
      (if friendly then quartetRightHeld D Q XR else quartetRightBadHeld D Q XL XR P) * b ^ 2 := by
  cases friendly <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairSquareMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-coordinate estimates for one moving bottom pair -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.pairSquareFintype
theorem sum_fieldPairCoefficientMoment {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ, fieldPairCoefficientMoment g χ d) = fieldPairMoment g d := by
  unfold fieldPairCoefficientMoment fieldPairMoment
  exact mellin_parseval (fun t : (ZMod p)ˣ => fieldBottomPairValue g d t)

theorem mellinCoefficient_mul_const {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)ˣ → ℂ) (c : ℂ) (χ : MulChar (ZMod p) ℂ) :
    mellinCoefficient (fun t => f t * c) χ = mellinCoefficient f χ * c := by
  unfold mellinCoefficient
  have ht (t : (ZMod p)ˣ) : f t * c * conj (χ t) = (f t * conj (χ t)) * c := by ring
  simp_rw [ht]
  rw [← Finset.sum_mul]
  ring

/-- Multiplication by the difference can be absorbed into the fixed square
coset; the zero difference is handled by the zero extension. -/
theorem fieldPair_scaled_square_coefficient_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) (K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
      fieldBottomPairValue g d ((K : ZMod p) * d * (r : ZMod p) ^ 2)) ρ‖ ^ 2 ≤
      2 * squareCharacterMass (fun χ => fieldPairCoefficientMoment g χ d) ρ := by
  classical
  by_cases hd : d = 0
  · simp [hd, mellinCoefficient, squareCharacterMass]
  · let k : (ZMod p)ˣ := K * Units.mk0 d hd
    have h := mellinCoefficient_square_pullback_bound Finset.univ
      (mellinCoefficient (fun t => fieldBottomPairValue g d t))
      (fun t => fieldBottomPairValue g d t)
      (fun t => (mellin_inversion (fun t => fieldBottomPairValue g d t) t).symm) k ρ
    simpa only [k, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
      fieldPairCoefficientMoment, squareCharacterMass] using h

theorem fieldPair_scaled_square_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) (K : (ZMod p)ˣ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ b : (ZMod p)ˣ, ‖fieldBottomPairValue g d
        ((K : ZMod p) * d * (b : ZMod p) ^ 2)‖ ^ 2) ≤ 2 * fieldPairMoment g d := by
  by_cases hd : d = 0
  · simp [hd]
  · let k : (ZMod p)ˣ := K * Units.mk0 d hd
    have h := sum_square_coset_le_twice k
      (fun t => ‖fieldBottomPairValue g d t‖ ^ 2) (fun _ => sq_nonneg _)
    have h' := mul_le_mul_of_nonneg_left h
      (show 0 ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ by positivity)
    simpa only [k, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
      fieldPairMoment, mul_left_comm] using h'

/-- First average the held pair's split, while the two pair differences
remain fixed. This costs two square fibers and the moving-pair coefficient. -/
theorem samePair_fixed_arguments_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (d e : ZMod p) (K L : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ b : (ZMod p)ˣ,
      ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
        fieldBottomPairValue g d ((K : ZMod p) * d * (r : ZMod p) ^ 2) *
        fieldBottomPairValue h e ((L : ZMod p) * e * (b : ZMod p) ^ 2)) ρ‖ ^ 2) ≤
      4 * squareCharacterMass (fun χ => fieldPairCoefficientMoment g χ d) ρ *
        fieldPairMoment h e := by
  let A := squareCharacterMass (fun χ => fieldPairCoefficientMoment g χ d) ρ
  have hA : 0 ≤ A := squareCharacterMass_nonneg _ (fun _ => sq_nonneg _) _
  simp_rw [mellinCoefficient_mul_const, norm_mul, mul_pow]
  calc
    _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ b : (ZMod p)ˣ,
        (2 * A) * ‖fieldBottomPairValue h e
          ((L : ZMod p) * e * (b : ZMod p) ^ 2)‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_right (fieldPair_scaled_square_coefficient_le g d K ρ)
          (sq_nonneg _)
    _ = (2 * A) * ((Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        ∑ b : (ZMod p)ˣ, ‖fieldBottomPairValue h e
          ((L : ZMod p) * e * (b : ZMod p) ^ 2)‖ ^ 2) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (2 * A) * (2 * fieldPairMoment h e) :=
      mul_le_mul_of_nonneg_left (fieldPair_scaled_square_mean_le h e L) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_SamePairHeldAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exposing the held product and split in a same-pair quartet -/

namespace Ostmann

open scoped BigOperators

theorem quartetRatioValue_samePair_coordinates {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (y K L q b r : (ZMod p)ˣ) :
    quartetRatioValue g h true true y (K * r ^ 2) (L * b ^ 2) q =
      if q = 1 then 0 else
        let d := (y : ZMod p) * (q : ZMod p) / ((q : ZMod p) - 1)
        fieldBottomPairValue g d ((K : ZMod p) * d * (r : ZMod p) ^ 2) *
          fieldBottomPairValue h (d - y)
            ((L : ZMod p) * (d - y) * (b : ZMod p) ^ 2) := by
  unfold quartetRatioValue ratioTest
  split_ifs
  · rfl
  · simp only [quartetLeftRatio, quartetRightRatio, ite_true, if_true, Units.val_mul,
      Units.val_pow_eq_pow_val]
    congr 2 <;> ring

/-- The two held averages cost four; the moving square pullback costs two.
All fixed unit parameters disappear from the resulting majorant. -/
theorem samePair_held_coefficient_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (y J K L : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          quartetRatioValue g h true true y (K * r ^ 2) (L * b ^ 2) (J * a ^ 2)) ρ‖ ^ 2) ≤
      8 * samePairMajorant (fieldPairCoefficientMoment g) (fieldPairMoment h) ρ y := by
  let A (d : ZMod p) := squareCharacterMass (fun χ => fieldPairCoefficientMoment g χ d) ρ
  let H (q : (ZMod p)ˣ) := if q = 1 then 0 else
    let d := (y : ZMod p) * (q : ZMod p) / ((q : ZMod p) - 1)
    A d * fieldPairMoment h (d - y)
  have hA (d : ZMod p) : 0 ≤ A d :=
    squareCharacterMass_nonneg _ (fun _ => sq_nonneg _) _
  have hH (q : (ZMod p)ˣ) : 0 ≤ H q := by
    dsimp [H]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hA _) (fieldPairMoment_nonneg h _)
  have hp (q : (ZMod p)ˣ) :
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          quartetRatioValue g h true true y (K * r ^ 2) (L * b ^ 2) q) ρ‖ ^ 2) ≤
        4 * H q := by
    simp_rw [quartetRatioValue_samePair_coordinates]
    by_cases hq : q = 1
    · simp [hq, H, mellinCoefficient]
    · simp only [hq, ite_false, if_false, H]
      simpa only [A, mul_assoc] using samePair_fixed_arguments_le g h
        ((y : ZMod p) * (q : ZMod p) / ((q : ZMod p) - 1))
        ((y : ZMod p) * (q : ZMod p) / ((q : ZMod p) - 1) - y) K L ρ
  have hsum : (∑ q : (ZMod p)ˣ, H q) =
      differenceMoment A (fieldPairMoment h) y := by
    have hzero : A 0 = 0 := by simp [A, squareCharacterMass]
    have hs := pair_ratio_sum_eq y A (fieldPairMoment h) hzero (fieldPairMoment_zero h)
    change (∑ q : (ZMod p)ˣ, H q) = ∑ x : ZMod p, A x * fieldPairMoment h (x - y)
    rw [← hs]
    apply Finset.sum_congr rfl
    intro q _
    dsimp [H]
    split_ifs with hq
    · rfl
    · have hq' : (q : ZMod p) ≠ 1 := fun h => hq (Units.ext h)
      have hd := pair_coordinate_difference (y : ZMod p) (q : ZMod p) hq'
      congr 2
      linear_combination hd
  calc
    _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ a : (ZMod p)ˣ, 4 * H (J * a ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun a _ => hp (J * a ^ 2)
    _ = 4 * (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ a : (ZMod p)ˣ, H (J * a ^ 2) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 4 * (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (2 * ∑ q : (ZMod p)ˣ, H q) :=
      mul_le_mul_of_nonneg_left (sum_square_coset_le_twice J H hH) (by positivity)
    _ = _ := by
      rw [hsum]
      change 4 * (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        (2 * differenceMoment A (fieldPairMoment h) y) =
        8 * ((Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * differenceMoment A (fieldPairMoment h) y)
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetRatioSwap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Swapping the two pairs and reversing the parent difference -/

namespace Ostmann

open scoped BigOperators

theorem quartetRatioValue_swap {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (y z t q : (ZMod p)ˣ) :
    quartetRatioValue g h true true y z t q =
      quartetRatioValue h g true true (-y) t z q⁻¹ := by
  by_cases hq : q = 1
  · simp [hq, quartetRatioValue, ratioTest]
  have hqi : q⁻¹ ≠ 1 := by simpa using hq
  have hqv : (q : ZMod p) ≠ 1 := fun h => hq (Units.ext h)
  have hden : (q : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr hqv
  have hi : (q : ZMod p)⁻¹ - 1 ≠ 0 := by
    intro he
    have he' : (q : ZMod p)⁻¹ = 1 := sub_eq_zero.mp he
    exact hqv (inv_eq_one.mp he')
  have hd : (-(y : ZMod p)) * (q : ZMod p)⁻¹ / ((q : ZMod p)⁻¹ - 1) =
      (y : ZMod p) * (q : ZMod p) / ((q : ZMod p) - 1) - y := by
    field_simp
    ring
  simp only [quartetRatioValue, ratioTest, hq, hqi, ite_false, if_false,
    Units.val_neg, Units.val_inv_eq_inv_val, hd,
    sub_neg_eq_add, sub_add_cancel, quartetLeftRatio, quartetRightRatio, ite_true, if_true]
  exact mul_comm _ _

/-- The same-pair estimate on the right is the left estimate with the
parent difference reversed and the product coordinate inverted. -/
theorem samePair_right_held_coefficient_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (y J K L : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          quartetRatioValue g h true true y (K * b ^ 2) (L * r ^ 2) (J * a ^ 2)) ρ‖ ^ 2) ≤
      8 * samePairMajorant (fieldPairCoefficientMoment h) (fieldPairMoment g) ρ (-y) := by
  have hfun (a b : (ZMod p)ˣ) :
      (fun r : (ZMod p)ˣ =>
        quartetRatioValue g h true true y (K * b ^ 2) (L * r ^ 2) (J * a ^ 2)) =
      (fun r : (ZMod p)ˣ =>
        quartetRatioValue h g true true (-y) (L * r ^ 2) (K * b ^ 2) (J * a ^ 2)⁻¹) :=
    funext fun r => quartetRatioValue_swap g h y _ _ _
  simp only [hfun]
  have hinv := (Equiv.inv (ZMod p)ˣ).bijective.sum_comp
    (fun a => (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
      ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
        quartetRatioValue h g true true (-y) (L * r ^ 2) (K * b ^ 2) (J⁻¹ * a ^ 2)) ρ‖ ^ 2)
  change (∑ a : (ZMod p)ˣ, _) = _ at hinv
  have hb := samePair_held_coefficient_le h g (-y) J⁻¹ L K ρ
  rw [← hinv] at hb
  simpa only [Equiv.inv_apply, mul_inv_rev, inv_pow, mul_comm J⁻¹, Units.val_neg] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetSamePairBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two moving leaves in the same bottom pair of an actual quartet -/

namespace Ostmann

open scoped BigOperators

theorem samePair_parent_ratio {p : ℕ} [Fact p.Prime]
    (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a : (ZMod p)ˣ) :
    (Q.sL / Q.sR) * (XR * Q.CR * a / (XL * Q.CL * (P / a))) =
      samePairParentMultiplier Q XL XR P * a ^ 2 := by
  apply Units.ext
  simp only [samePairParentMultiplier, Units.val_mul, Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val]
  field_simp

theorem samePair_right_parent_ratio {p : ℕ} [Fact p.Prime]
    (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a : (ZMod p)ˣ) :
    (Q.sL / Q.sR) * (XR * Q.CR * (P * a) / (XL * Q.CL * a⁻¹)) =
      samePairRightParentMultiplier Q XL XR P * a ^ 2 := by
  apply Units.ext
  simp only [samePairRightParentMultiplier, Units.val_mul, Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CrossQuartetFiber
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact product-fiber coordinates for the cross-pair coefficient bounds -/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.zeroTupleCommGroup
theorem crossQuartetFiberEquiv_symm {U : Type*} [CommGroup U]
    (left right : Bool) (P a b r : U) :
    ((crossQuartetFiberEquiv left right P).symm (a, b, r)).1 =
      crossQuartetLeaves left right P a b r := by
  cases left <;> cases right <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedQuartetBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local bounds for every opposite sibling conjugation choice -/

namespace Ostmann

open scoped BigOperators

theorem crossQuartetLeaves_amplitude_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P a b r : (ZMod p)ˣ) (cL cR left right : Bool) :
    rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
      (crossQuartetLeaves left right P a b r) =
    quartetRatioValue (orientedPairBase (pairConjugate g cL) left)
      (orientedPairBase (pairConjugate g cR) right) left right
      (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
      ((if left then quartetLeftHeld D Q XL else quartetLeftBadHeld D Q XL XR P) * a ^ 2)
      ((if right then quartetRightHeld D Q XR else quartetRightBadHeld D Q XL XR P) * b ^ 2)
      (quartetMovingMultiplier Q XL XR P a * r ^ 2) := by
  change rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
    (((crossLeftLeaves left a r).1, (crossLeftLeaves left a r).2),
      ((crossRightLeaves right P a b r).1, (crossRightLeaves right P a b r).2)) = _
  rw [rationalTreeAmplitude_quartet_conjugation, rationalQuartetPairsValue_oriented]
  rw [crossLeftLeaves_product, crossRightLeaves_product, quartet_friendly_product]
  rw [crossLeftLeaves_parameter, crossRightLeaves_parameter, quartet_friendly_ratio]

theorem rationalQuartet_cross_held_bound_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (cL cR left right : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
            (crossQuartetLeaves left right P a b r)) ρ‖ ^ 2) ≤
    8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
      crossPairMajorant (orientedPairBase (pairConjugate g cL) left)
        (orientedPairBase (pairConjugate g cR) right) left right ρ⁻¹
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  simp_rw [crossQuartetLeaves_amplitude_conjugation]
  exact crossPair_held_coefficient_le _ _ left right _ _ _
    (fun a _b => quartetMovingMultiplier Q XL XR P a) ρ

theorem samePairLeftLeaves_amplitude_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P a b r : (ZMod p)ˣ) (cL cR : Bool) :
    rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
      (samePairLeftLeaves P a b r) =
    quartetRatioValue (pairConjugate g cL) (pairConjugate g cR) true true
      (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
      (quartetLeftHeld D Q XL * r ^ 2) (quartetRightHeld D Q XR * b ^ 2)
      (samePairParentMultiplier Q XL XR P * a ^ 2) := by
  change rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
    ((P / (a * r), r), (a / b, b)) = _
  rw [rationalTreeAmplitude_quartet_conjugation,
    rationalQuartetPairsValue_oriented _ _ D Q _ _ _ _ _ _ true true]
  rw [samePair_total_product, samePair_left_product, div_mul_cancel, samePair_parent_ratio]
  rfl

theorem rationalQuartet_samePair_left_held_bound_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (cL cR : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
            (samePairLeftLeaves P a b r)) ρ‖ ^ 2) ≤
      8 * samePairMajorant (fieldPairCoefficientMoment (pairConjugate g cL))
        (fieldPairMoment (pairConjugate g cR)) ρ
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  simp_rw [samePairLeftLeaves_amplitude_conjugation]
  exact samePair_held_coefficient_le _ _ _ _ _ _ ρ

theorem samePairRightLeaves_amplitude_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P a b r : (ZMod p)ˣ) (cL cR : Bool) :
    rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
      (samePairRightLeaves P a b r) =
    quartetRatioValue (pairConjugate g cL) (pairConjugate g cR) true true
      (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
      (quartetLeftHeld D Q XL * b ^ 2) (quartetRightHeld D Q XR * r ^ 2)
      (samePairRightParentMultiplier Q XL XR P * a ^ 2) := by
  change rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
    ((a⁻¹ / b, b), (P * a / r, r)) = _
  rw [rationalTreeAmplitude_quartet_conjugation,
    rationalQuartetPairsValue_oriented _ _ D Q _ _ _ _ _ _ true true]
  rw [samePair_right_total_product, div_mul_cancel, div_mul_cancel, samePair_right_parent_ratio]
  rfl

theorem rationalQuartet_samePair_right_held_bound_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (cL cR : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
            (samePairRightLeaves P a b r)) ρ‖ ^ 2) ≤
      8 * samePairMajorant (fieldPairCoefficientMoment (pairConjugate g cR))
        (fieldPairMoment (pairConjugate g cL)) ρ
        (-rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  simp_rw [samePairRightLeaves_amplitude_conjugation]
  exact samePair_right_held_coefficient_le _ _ _ _ _ _ ρ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairCoefficientMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small individual and bounded total means of pair coefficients -/

namespace Ostmann

open scoped BigOperators

theorem autocorrelation_energy_le_fourier_sup {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hflat : ∀ a, ‖additiveFourier f a‖ ≤ ε) :
    (∑ d : ZMod p, ‖additiveAutocorrelation f d‖ ^ 2) ≤
      ε ^ 2 * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  rw [additiveFourier_energy (additiveAutocorrelation f)]
  simp only [additiveFourier_autocorrelation, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (p : ℝ) * ∑ a : ZMod p, ε ^ 2 * ‖additiveFourier f a‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro a _
      rw [pow_two (‖additiveFourier f a‖ ^ 2)]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hε).mpr (hflat a)) (sq_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum, mul_left_comm, ← additiveFourier_energy f]

theorem fieldPairCoefficientMoment_le_autocorrelation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (d : ZMod p) :
    fieldPairCoefficientMoment g χ d ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        ‖additiveAutocorrelation (characterTwist g χ) d‖ ^ 2 := by
  by_cases hd : d = 0
  · rw [hd, fieldPairCoefficientMoment_zero]
    positivity
  · let du : (ZMod p)ˣ := Units.mk0 d hd
    have he : (fun t : (ZMod p)ˣ => fieldBottomPairValue g d t) = bottomPairValue g du := by
      funext t
      simp only [fieldBottomPairValue, hd, Units.ne_zero, dite_false, Units.mk0_val, du]
    unfold fieldPairCoefficientMoment
    rw [he, bottomPair_mellin_autocorrelation]
    simp only [norm_mul, norm_div, Complex.norm_natCast, mul_pow, du, Units.val_mk0]
    exact le_rfl

theorem fieldPairCoefficientMoment_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (χ : MulChar (ZMod p) ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : ∀ a, ‖additiveFourier (characterTwist g χ) a‖ ≤ ε)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ d : ZMod p, fieldPairCoefficientMoment g χ d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 3 * ε ^ 2 := by
  have hnorm (x : ZMod p) : ‖characterTwist g χ x‖ = ‖g x‖ := by
    by_cases hx : x = 0
    · simp [hx, characterTwist, hg]
    · have hn := norm_mulChar_unit χ (Units.mk0 x hx)
      simpa only [characterTwist, norm_mul, Complex.norm_conj, Units.val_mk0, hn, mul_one]
        using congrArg (fun t : ℝ => ‖g x‖ * t) hn
  have hauto := autocorrelation_energy_le_fourier_sup (characterTwist g χ) ε hε hflat
  simp_rw [hnorm] at hauto
  have hsum := (Finset.sum_le_sum fun d (_ : d ∈ (Finset.univ : Finset (ZMod p))) =>
    fieldPairCoefficientMoment_le_autocorrelation g χ d)
  rw [← Finset.mul_sum] at hsum
  have hU : 0 ≤ (Fintype.card (ZMod p)ˣ : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 * (ε ^ 2 * p)) /
        (Fintype.card (ZMod p)ˣ : ℝ) := by
      apply div_le_div_of_nonneg_right _ hU
      exact hsum.trans (mul_le_mul_of_nonneg_left
        (hauto.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg _))) (sq_nonneg _))
    _ = _ := by ring

attribute [local instance] OAI.Ostmann.pairCoefficientMeansFintype
theorem fieldPairCoefficientMoment_total_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ χ : MulChar (ZMod p) ℂ,
      (∑ d : ZMod p, fieldPairCoefficientMoment g χ d) /
        (Fintype.card (ZMod p)ˣ : ℝ)) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [sum_fieldPairCoefficientMoment]
  exact fieldPairMoment_mean_le g hg henergy

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ConjugatedPairMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same-pair bounds uniformly in the manuscript's conjugation choices -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem norm_pairConjugate {p : ℕ} (g : ZMod p → ℂ) (c : Bool) (x : ZMod p) :
    ‖pairConjugate g c x‖ = ‖g x‖ := by cases c <;> simp [pairConjugate]

theorem pairConjugate_zero {p : ℕ} (g : ZMod p → ℂ) (hg : g 0 = 0) (c : Bool) :
    pairConjugate g c 0 = 0 := by cases c <;> simp [pairConjugate, hg]

theorem MixedFourierBound.pairConjugate {p : ℕ} [Fact p.Prime]
    {g : ZMod p → ℂ} {ε : ℝ} (hg : MixedFourierBound g ε) (c : Bool) :
    MixedFourierBound (pairConjugate g c) ε := by
  cases c
  · exact hg
  · exact hg.conj

theorem MixedFourierBound.characterTwist {p : ℕ} [Fact p.Prime]
    {g : ZMod p → ℂ} {ε : ℝ} (hg : MixedFourierBound g ε)
    (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    ‖additiveFourier (characterTwist g χ) a‖ ≤ ε := by
  have he : Ostmann.characterTwist g χ = fun x => g x * χ⁻¹ x := by
    funext x
    exact congrArg (fun z => g x * z) (MulChar.star_apply' χ x)
  rw [he]
  exact hg χ⁻¹ a

theorem conjugated_samePairMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (ε : ℝ) (hε : 0 ≤ ε)
    (hflat : MixedFourierBound g ε)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (cL cR : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, samePairMajorant
      (fieldPairCoefficientMoment (pairConjugate g cL))
      (fieldPairMoment (pairConjugate g cR)) ρ y) / (Fintype.card (ZMod p)ˣ : ℝ) ≤
      2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 5 * ε ^ 2 := by
  have he (c : Bool) : (∑ x : ZMod p, ‖pairConjugate g c x‖ ^ 2) ≤ (p : ℝ) := by
    simpa only [norm_pairConjugate] using henergy
  have h := samePairMajorant_mean_le
    (fieldPairCoefficientMoment (pairConjugate g cL))
    (fieldPairMoment (pairConjugate g cR)) (fun _ _ => sq_nonneg _)
    (fieldPairMoment_nonneg _) (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 3 * ε ^ 2)
    (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2) (by positivity)
    (fun χ => fieldPairCoefficientMoment_mean_le _ (pairConjugate_zero g hg cL) χ ε hε
      ((hflat.pairConjugate cL).characterTwist χ) (he cL))
    (fieldPairMoment_mean_le _ (pairConjugate_zero g hg cR) (he cR)) ρ
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

attribute [local instance] OAI.Ostmann.conjugatedPairMeansFintype
theorem conjugated_samePairMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) (cL cR : Bool) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ, samePairMajorant
      (fieldPairCoefficientMoment (pairConjugate g cL))
      (fieldPairMoment (pairConjugate g cR)) ρ y) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 := by
  have he (c : Bool) : (∑ x : ZMod p, ‖pairConjugate g c x‖ ^ 2) ≤ (p : ℝ) := by
    simpa only [norm_pairConjugate] using henergy
  have h := samePairMajorant_total_mean_le
    (fieldPairCoefficientMoment (pairConjugate g cL))
    (fieldPairMoment (pairConjugate g cR)) (fun _ _ => sq_nonneg _)
    (fieldPairMoment_nonneg _) (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2)
    (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2) (sq_nonneg _)
    (fieldPairCoefficientMoment_total_mean_le _ (pairConjugate_zero g hg cL) (he cL))
    (fieldPairMoment_mean_le _ (pairConjugate_zero g hg cR) (he cR))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TwoBadFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Joining the four cases of the two-bad quartet sum

The nonprincipal part uses the fourth moment. The two cases with exactly
one principal twist use its total energy and the other twist's maximum.
The last case uses the principal maximum and a single energy bound.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.twoBadFintype
attribute [local instance] OAI.Ostmann.twoBadDecidableEq
/-- A common fourth-moment bound controls all nonprincipal terms. -/
theorem two_bad_nonprincipal_le {p : ℕ} [Fact p.Prime]
    (F G : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (ν : MulChar (ZMod p) ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hF : (∑ χ : MulChar (ZMod p) ℂ,
      ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖F χ α a‖ ^ 4) ≤ T)
    (hG : (∑ ψ : MulChar (ZMod p) ℂ,
      ∑ β ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖G ψ β a‖ ^ 4) ≤ T) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
        ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0) ≤ T := by
  have hFn : 0 ≤ ∑ χ : MulChar (ZMod p) ℂ,
      ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖F χ α a‖ ^ 4 := by positivity
  have hGn : 0 ≤ ∑ ψ : MulChar (ZMod p) ℂ,
      ∑ β ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖G ψ β a‖ ^ 4 := by positivity
  have h := (two_bad_twist_cauchy F G ν).trans (mul_le_mul hF hG hGn hT)
  nlinarith

/-- The complete two-bad sum, including both principal-character exceptions. -/
theorem two_bad_fourier_sum_le {p : ℕ} [Fact p.Prime]
    (F G : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (ν : MulChar (ZMod p) ℂ) (T K M R S : ℝ)
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hF4 : (∑ χ : MulChar (ZMod p) ℂ,
      ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖F χ α a‖ ^ 4) ≤ T)
    (hG4 : (∑ ψ : MulChar (ZMod p) ℂ,
      ∑ β ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖G ψ β a‖ ^ 4) ≤ T)
    (hFn : ∀ χ α, α ≠ 1 → ∀ a, ‖F χ α a‖ ^ 2 ≤ K)
    (hGn : ∀ ψ β, β ≠ 1 → ∀ a, ‖G ψ β a‖ ^ 2 ≤ K)
    (hFp : ∀ χ a, ‖F χ 1 a‖ ^ 2 ≤ M)
    (hFsum : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖F χ 1 a‖ ^ 2) ≤ S)
    (hGsum : (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖G ψ 1 a‖ ^ 2) ≤ S)
    (hGenergy : ∀ ψ, (∑ a : ZMod p, ‖G ψ 1 a‖ ^ 2) ≤ R) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2) ≤
      T + 2 * K * S + M * R := by
  classical
  let n := ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
    if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
      ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0
  have hn : n ≤ T := two_bad_nonprincipal_le F G ν T hT hF4 hG4
  have hneg (ψ : MulChar (ZMod p) ℂ) :
      (∑ a : ZMod p, ‖G ψ 1 (-a)‖ ^ 2) = ∑ a : ZMod p, ‖G ψ 1 a‖ ^ 2 :=
    (Equiv.neg (ZMod p)).bijective.sum_comp (fun a => ‖G ψ 1 a‖ ^ 2)
  have hp (χ ψ : MulChar (ZMod p) ℂ) (a : ZMod p) :
      ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 ≤
        (if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
          ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0) +
        (if ψ = ν then K * ‖F χ 1 a‖ ^ 2 else 0) +
        (if χ = ν⁻¹ then K * ‖G ψ 1 (-a)‖ ^ 2 else 0) +
        (if χ = ν⁻¹ ∧ ψ = ν then M * ‖G ψ 1 (-a)‖ ^ 2 else 0) := by
    by_cases hα : ν * ψ⁻¹ = 1 <;> by_cases hβ : ν⁻¹ * χ⁻¹ = 1
    · have hψ : ψ = ν := (mul_inv_eq_one.mp hα).symm
      have hχ : χ = ν⁻¹ := (mul_inv_eq_one.mp hβ).symm
      simp [hχ, hψ]
      have h := mul_le_mul_of_nonneg_right (hFp ν⁻¹ a) (sq_nonneg ‖G ν 1 (-a)‖)
      have h₁ := mul_nonneg hK (sq_nonneg ‖F ν⁻¹ 1 a‖)
      have h₂ := mul_nonneg hK (sq_nonneg ‖G ν 1 (-a)‖)
      linarith
    · have hψ : ψ = ν := (mul_inv_eq_one.mp hα).symm
      have hχ : χ ≠ ν⁻¹ := by intro h; apply hβ; simp [h]
      simpa [hψ, hχ, hβ, mul_comm] using
        mul_le_mul_of_nonneg_right (hGn ν _ hβ (-a)) (sq_nonneg ‖F χ 1 a‖)
    · have hψ : ψ ≠ ν := by intro h; apply hα; simp [h]
      have hχ : χ = ν⁻¹ := (mul_inv_eq_one.mp hβ).symm
      simpa [hχ, hψ, hα] using
        mul_le_mul_of_nonneg_right (hFn ν⁻¹ _ hα a) (sq_nonneg ‖G ψ 1 (-a)‖)
    · have hψ : ψ ≠ ν := by intro h; apply hα; simp [h]
      have hχ : χ ≠ ν⁻¹ := by intro h; apply hβ; simp [h]
      simp [hα, hβ, hψ, hχ]
  calc
    _ ≤ n + K * (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖F χ 1 a‖ ^ 2) +
        K * (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, ‖G ψ 1 a‖ ^ 2) +
        M * (∑ a : ZMod p, ‖G ν 1 a‖ ^ 2) := by
      calc
        _ ≤ ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
            ((if ν * ψ⁻¹ ≠ 1 ∧ ν⁻¹ * χ⁻¹ ≠ 1 then
              ‖F χ (ν * ψ⁻¹) a‖ ^ 2 * ‖G ψ (ν⁻¹ * χ⁻¹) (-a)‖ ^ 2 else 0) +
            (if ψ = ν then K * ‖F χ 1 a‖ ^ 2 else 0) +
            (if χ = ν⁻¹ then K * ‖G ψ 1 (-a)‖ ^ 2 else 0) +
            (if χ = ν⁻¹ ∧ ψ = ν then M * ‖G ψ 1 (-a)‖ ^ 2 else 0)) :=
          Finset.sum_le_sum fun χ _ => Finset.sum_le_sum fun ψ _ =>
            Finset.sum_le_sum fun a _ => hp χ ψ a
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel,
            Finset.sum_const_zero, n]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
          simp only [← Finset.mul_sum, hneg]
          simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    _ ≤ T + K * S + K * S + M * R := by
      exact add_le_add (add_le_add (add_le_add hn
        (mul_le_mul_of_nonneg_left hFsum hK))
        (mul_le_mul_of_nonneg_left hGsum hK))
        (mul_le_mul_of_nonneg_left (hGenergy ν) hM)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetSpectrumBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-bad quartet estimate in terms of its spectra

The hypotheses are the nonnegative spectrum bounds `src40`. This combines
the previously proved Gauss fourth moment with all principal corrections.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetSpectrumDecidableEq_rfc8d08_1 {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _
theorem norm_at_zero_le_spectrum_mass {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ a, additiveFourier f a = (w a : ℂ)) (hw : ∀ a, 0 ≤ w a) :
    ‖f 0‖ ≤ ∑ a : ZMod p, w a := by
  rw [additiveFourier_inversion f 0]
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one, hf]
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)] using
    norm_sum_le (Finset.univ : Finset (ZMod p)) (fun a => (w a : ℂ))

theorem principal_fourier_norm_sq_le {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ a, additiveFourier f a = (w a : ℂ)) (hw : ∀ a, 0 ≤ w a)
    (J W : ℝ) (hmass : (∑ a : ZMod p, w a) ≤ J) (hmax : ∀ a, w a ≤ W)
    (a : ZMod p) :
    ‖additiveFourier (fun x => f x * (1 : MulChar (ZMod p) ℂ) x) a‖ ^ 2 ≤
      (W + (p : ℝ)⁻¹ * J) ^ 2 := by
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [additiveFourier_principal_twist, hf]
  calc
    _ ≤ ‖(w a : ℂ)‖ + ‖(p : ℂ)⁻¹ * f 0‖ := norm_sub_le _ _
    _ = w a + (p : ℝ)⁻¹ * ‖f 0‖ := by
      simp only [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hw a)]
    _ ≤ W + (p : ℝ)⁻¹ * J := add_le_add (hmax a)
      (mul_le_mul_of_nonneg_left ((norm_at_zero_le_spectrum_mass f w hf hw).trans hmass)
        (inv_nonneg.mpr (Nat.cast_nonneg p)))

theorem character_spectrum_energy_le {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ a, additiveFourier f a = (w a : ℂ))
    (α : MulChar (ZMod p) ℂ) :
    (∑ a : ZMod p, ‖additiveFourier (fun x => f x * α x) a‖ ^ 2) ≤
      ∑ a : ZMod p, w a ^ 2 := by
  have h := additiveFourier_character_energy_le f α
  simpa only [hf, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

attribute [local instance] OAI.Ostmann.quartetSpectrumFintype
/-- Complete bound for the two-bad row of `tree-twisted-convolution`. -/
theorem two_bad_spectrum_sum_le {p : ℕ} [Fact p.Prime]
    (f g : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (w v : MulChar (ZMod p) ℂ → ZMod p → ℝ)
    (hf : ∀ χ a, additiveFourier (f χ) a = (w χ a : ℂ))
    (hg : ∀ χ a, additiveFourier (g χ) a = (v χ a : ℂ))
    (hw : ∀ χ a, 0 ≤ w χ a) (hv : ∀ χ a, 0 ≤ v χ a)
    (J W R S : ℝ) (hR : 0 ≤ R)
    (hwmass : ∀ χ, (∑ a : ZMod p, w χ a) ≤ J)
    (hvmass : ∀ χ, (∑ a : ZMod p, v χ a) ≤ J)
    (hwmax : ∀ χ a, w χ a ≤ W)
    (hwr : ∀ χ, (∑ a : ZMod p, w χ a ^ 2) ≤ R)
    (hvr : ∀ χ, (∑ a : ZMod p, v χ a ^ 2) ≤ R)
    (hws : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, w χ a ^ 2) ≤ S)
    (hvs : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, v χ a ^ 2) ≤ S)
    (ν : MulChar (ZMod p) ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (fun x => f χ x * (ν * ψ⁻¹) x) a‖ ^ 2 *
        ‖additiveFourier (fun x => g ψ x * (ν⁻¹ * χ⁻¹) x) (-a)‖ ^ 2) ≤
      (2 * ((Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ)) * R * S +
        3 * ((Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ) ^ 2) * J ^ 4) +
      2 * ((p : ℝ)⁻¹ * J ^ 2) * S + (W + (p : ℝ)⁻¹ * J) ^ 2 * R := by
  have hS : 0 ≤ S := (by positivity :
    0 ≤ ∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, w χ a ^ 2).trans hws
  apply two_bad_fourier_sum_le
    (fun χ α a => additiveFourier (fun x => f χ x * α x) a)
    (fun ψ β a => additiveFourier (fun x => g ψ x * β x) a) ν
  · positivity
  · positivity
  · positivity
  · exact nonprincipal_fourth_family_bound f w hf hw J R S hR hwmass hwr hws
  · exact nonprincipal_fourth_family_bound g v hg hv J R S hR hvmass hvr hvs
  · intro χ α hα a
    exact nonprincipal_fourier_norm_sq_le (f χ) (w χ) (hf χ) (hw χ) J (hwmass χ) α hα a
  · intro ψ β hβ a
    exact nonprincipal_fourier_norm_sq_le (g ψ) (v ψ) (hg ψ) (hv ψ) J (hvmass ψ) β hβ a
  · intro χ a
    exact principal_fourier_norm_sq_le (f χ) (w χ) (hf χ) (hw χ) J W (hwmass χ) (hwmax χ) a
  · exact (Finset.sum_le_sum fun χ _ => character_spectrum_energy_le (f χ) (w χ) (hf χ) 1).trans hws
  · exact (Finset.sum_le_sum fun ψ _ => character_spectrum_energy_le (g ψ) (v ψ) (hg ψ) 1).trans hvs
  · intro ψ
    exact (character_spectrum_energy_le (g ψ) (v ψ) (hg ψ) 1).trans (hvr ψ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairFourierMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete Fourier mass bounds needed in the cross-pair application -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem norm_characterTwist_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (x : ZMod p) :
    ‖characterTwist g χ x‖ ≤ ‖g x‖ := by
  by_cases hx : x = 0
  · simp [hx, characterTwist, MulChar.map_zero]
  · have hn := norm_mulChar_unit χ (Units.mk0 x hx)
    simp only [characterTwist, norm_mul, Complex.norm_conj, Units.val_mk0] at hn ⊢
    rw [hn, mul_one]

theorem characterTwist_energy_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) :
    (∑ x : ZMod p, ‖characterTwist g χ x‖ ^ 2) ≤ ∑ x : ZMod p, ‖g x‖ ^ 2 := by
  exact Finset.sum_le_sum fun x _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_characterTwist_le g χ x) 2

theorem pairAutocorrelation_fourier_formula {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    additiveFourier (pairAutocorrelation g χ) a =
      (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) *
        ‖additiveFourier (characterTwist g χ) a‖ ^ 2 : ℝ) : ℂ) := by
  change additiveFourier (fun d => (p : ℂ) / (Fintype.card (ZMod p)ˣ : ℂ) *
    additiveAutocorrelation (characterTwist g χ) d) a = _
  rw [additiveFourier_const_mul, additiveFourier_autocorrelation]
  push_cast
  rfl

theorem pairAutocorrelation_weight_mass_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ a : ZMod p, (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) *
      ‖additiveFourier (characterTwist g χ) a‖ ^ 2) ≤
        (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) := by
  rw [← Finset.mul_sum, additiveFourier_parseval]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h := (characterTwist_energy_le g χ).trans henergy
  calc
    _ ≤ (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) * ((p : ℝ)⁻¹ * p) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) (by positivity)
    _ = _ := by rw [inv_mul_cancel₀ hp, mul_one]

theorem pairAutocorrelation_zero_norm_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    ‖pairAutocorrelation g χ 0‖ ≤ (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) := by
  exact (norm_at_zero_le_spectrum_mass _ _ (pairAutocorrelation_fourier_formula g χ)
    (fun _ => by positivity)).trans (pairAutocorrelation_weight_mass_le g χ henergy)

theorem fieldPairCoefficientMoment_eq_pairAutocorrelation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (d : ZMod p) (hd : d ≠ 0) :
    fieldPairCoefficientMoment g χ d = ‖pairAutocorrelation g χ d‖ ^ 2 := by
  let du : (ZMod p)ˣ := Units.mk0 d hd
  have he : (fun t : (ZMod p)ˣ => fieldBottomPairValue g d t) = bottomPairValue g du := by
    funext t
    simp only [fieldBottomPairValue, hd, Units.ne_zero, dite_false, Units.mk0_val, du]
  unfold fieldPairCoefficientMoment
  rw [he, bottomPair_mellin_autocorrelation]
  rfl

theorem pairAutocorrelation_point_energy_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) (d : ZMod p) :
    ‖pairAutocorrelation g χ d‖ ^ 2 ≤ fieldPairCoefficientMoment g χ d +
      if d = 0 then ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 else 0 := by
  by_cases hd : d = 0
  · simp only [hd, fieldPairCoefficientMoment_zero, ite_true, if_true, zero_add]
    exact pow_le_pow_left₀ (norm_nonneg _) (pairAutocorrelation_zero_norm_le g χ henergy) 2
  · rw [fieldPairCoefficientMoment_eq_pairAutocorrelation g χ d hd, ite_eq_right hd, add_zero]

theorem pairAutocorrelation_fourier_energy_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hflat : MixedFourierBound g ε)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ a : ZMod p, ‖additiveFourier (pairAutocorrelation g χ) a‖ ^ 2) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 * ε ^ 2 := by
  have hauto := autocorrelation_energy_le_fourier_sup (characterTwist g χ) ε hε
    (hflat.characterTwist χ)
  have he := (characterTwist_energy_le g χ).trans henergy
  rw [additiveFourier_parseval]
  have hP (d : ZMod p) : ‖pairAutocorrelation g χ d‖ ^ 2 =
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        ‖additiveAutocorrelation (characterTwist g χ) d‖ ^ 2 := by
    simp only [pairAutocorrelation, norm_mul, norm_div, Complex.norm_natCast, mul_pow]
  simp_rw [hP]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (p : ℝ)⁻¹ * (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 * (ε ^ 2 * p)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (hauto.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))) (sq_nonneg _)
    _ = _ := by
      have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      field_simp

attribute [local instance] OAI.Ostmann.pairFourierMassFintype
theorem pairAutocorrelation_total_point_energy_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ d : ZMod p, ‖pairAutocorrelation g χ d‖ ^ 2) ≤
      2 * (Fintype.card (ZMod p)ˣ : ℝ) *
        ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (MulChar (ZMod p) ℂ)))
    (fun χ _ => Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod p)))
      (fun d _ => pairAutocorrelation_point_energy_le g χ henergy d))
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_mulChar_eq_card_units] at h
  have hF : (∑ χ : MulChar (ZMod p) ℂ, ∑ d : ZMod p, fieldPairCoefficientMoment g χ d) =
      ∑ d : ZMod p, fieldPairMoment g d := by
    rw [Finset.sum_comm]
    simp_rw [sum_fieldPairCoefficientMoment]
  rw [hF] at h
  have hU : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hR := (div_le_iff₀ hU).mp (fieldPairMoment_mean_le g hg henergy)
  nlinarith

theorem pairAutocorrelation_total_fourier_energy_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (pairAutocorrelation g χ) a‖ ^ 2) ≤
      2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) := by
  simp_rw [additiveFourier_parseval]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (pairAutocorrelation_total_point_energy_le g hg henergy)
    (show 0 ≤ (p : ℝ)⁻¹ by positivity)).trans_eq
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ConcreteQuartetFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quartet Fourier estimate with the actual autocorrelation spectra -/

namespace Ostmann

open scoped BigOperators

theorem twoBadQuartetError_nonneg (p : ℕ) [Fact p.Prime] (ε : ℝ) :
    0 ≤ twoBadQuartetError p ε := by unfold twoBadQuartetError; positivity

attribute [local instance] OAI.Ostmann.concreteQuartetFintype
theorem concrete_two_bad_fourier_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0) (hh : h 0 = 0)
    (heg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (heh : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hfg : MixedFourierBound g ε) (hfh : MixedFourierBound h ε)
    (ν : MulChar (ZMod p) ℂ) :
    quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) false false ν ≤
      twoBadQuartetError p ε := by
  let U : ℝ := Fintype.card (ZMod p)ˣ
  let C : ℝ := p / U
  let w (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : ℝ :=
    C * ‖additiveFourier (characterTwist f χ) a‖ ^ 2
  have hweight (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
      additiveFourier (pairAutocorrelation f χ) a = (w f χ a : ℂ) :=
    pairAutocorrelation_fourier_formula f χ a
  have hn (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : 0 ≤ w f χ a := by
    dsimp [w, C, U]
    positivity
  have hmass (f : ZMod p → ℂ) (he : (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ (p : ℝ))
      (χ : MulChar (ZMod p) ℂ) : (∑ a : ZMod p, w f χ a) ≤ C :=
    pairAutocorrelation_weight_mass_le f χ he
  have hmax (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : w g χ a ≤ C * ε ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by dsimp [C, U]; positivity)
    exact (sq_le_sq₀ (norm_nonneg _) hε).mpr (hfg.characterTwist χ a)
  have hrow (f : ZMod p → ℂ) (he : (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ (p : ℝ))
      (hf : MixedFourierBound f ε) (χ : MulChar (ZMod p) ℂ) :
      (∑ a : ZMod p, w f χ a ^ 2) ≤ C ^ 2 * ε ^ 2 := by
    have hb := pairAutocorrelation_fourier_energy_le f χ ε hε hf he
    simpa only [hweight, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hb
  have htotal (f : ZMod p → ℂ) (hf : f 0 = 0)
      (he : (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ (p : ℝ)) :
      (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, w f χ a ^ 2) ≤ 2 * C := by
    have hb := pairAutocorrelation_total_fourier_energy_le f hf he
    simpa only [hweight, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hb
  have hb := two_bad_spectrum_sum_le (pairAutocorrelation g) (pairAutocorrelation h)
    (w g) (w h) (hweight g) (hweight h) (hn g) (hn h)
    C (C * ε ^ 2) (C ^ 2 * ε ^ 2) (2 * C) (by positivity)
    (hmass g heg) (hmass h heh) hmax (hrow g heg hfg) (hrow h heh hfh)
    (htotal g hg heg) (htotal h hh heh) ν
  simpa only [quartetFourierEnergy, quartetLeftTwist, quartetRightTwist,
    Bool.false_eq_true, ite_false, if_false, mul_one, twoBadQuartetError] using hb

theorem friendlyQuartetError_nonneg (p : ℕ) [Fact p.Prime] (ε : ℝ) :
    0 ≤ friendlyQuartetError p ε := by unfold friendlyQuartetError; positivity

theorem concrete_left_friendly_fourier_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0) (hh : h 0 = 0)
    (heg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (heh : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hfg : MixedFourierBound g ε) (right : Bool) (ν : MulChar (ZMod p) ℂ) :
    quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) true right ν ≤
      friendlyQuartetError p ε := by
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  have hb := left_friendly_fourier_sum_le (pairAutocorrelation g) (pairAutocorrelation h)
    (((p : ℝ) / ((p : ℝ) - 1)) * (ε ^ 4 + Real.sqrt (3 / (p : ℝ))))
    (2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)))
    (by rw [← hU]; positivity)
    (fun η a => uniform_mellin_bound_of_fourier_bound g hg heg ε hfg η a)
    (pairAutocorrelation_total_fourier_energy_le h hh heh) right ν
  apply hb.trans_eq
  dsimp [friendlyQuartetError]
  rw [hU]
  ring

theorem concrete_quartet_fourier_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0) (hh : h 0 = 0)
    (heg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (heh : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hfg : MixedFourierBound g ε) (hfh : MixedFourierBound h ε)
    (left right : Bool) (ν : MulChar (ZMod p) ℂ) :
    quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) left right ν ≤
      friendlyQuartetError p ε + twoBadQuartetError p ε := by
  cases left
  · cases right
    · exact (concrete_two_bad_fourier_le g h hg hh heg heh ε hε hfg hfh ν).trans
        (le_add_of_nonneg_left (friendlyQuartetError_nonneg p ε))
    · rw [quartetFourierEnergy_swap]
      exact (concrete_left_friendly_fourier_le h g hh hg heh heg ε hfh false ν⁻¹).trans
        (le_add_of_nonneg_right (twoBadQuartetError_nonneg p ε))
  · exact (concrete_left_friendly_fourier_le g h hg hh heg heh ε hfg right ν).trans
      (le_add_of_nonneg_right (twoBadQuartetError_nonneg p ε))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CycleMellin
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Mellin constraint retained by cycle averaging

Reciprocal multiplication retains exactly the character tuples whose
signed product is principal. This is the relation used in the final
cycle-coefficient estimate.
-/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.cycleMellinDecidableEq
private theorem mulChar_product_apply {p : ℕ} [Fact p.Prime]
    {I : Type*} (s : Finset I) (χ : I → MulChar (ZMod p) ℂ) (z : (ZMod p)ˣ) :
    (∏ i ∈ s, χ i) z = ∏ i ∈ s, χ i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MulChar.one_apply_coe]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, MulChar.coeToFun_mul, Pi.mul_apply, ih]

attribute [local instance] OAI.Ostmann.cycleMellinFintype
theorem cycleAverage_product_mellin {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → (ZMod p)ˣ → ℂ) (sign : I → ℤ) (m : I → (ZMod p)ˣ) :
    cycleAverage sign (fun m => ∏ i : I, f i (m i)) m =
      ∑ ρ : I → MulChar (ZMod p) ℂ,
        if (∏ i : I, (ρ i) ^ sign i) = 1 then
          ∏ i : I, mellinCoefficient (f i) (ρ i) * ρ i (m i) else 0 := by
  classical
  have hc : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (z : (ZMod p)ˣ) :
      (∏ i : I, f i (cycleMultiply sign z m i)) =
        ∑ ρ : I → MulChar (ZMod p) ℂ,
          (∏ i : I, mellinCoefficient (f i) (ρ i) * ρ i (m i)) *
            (∏ i : I, (ρ i) ^ sign i) z := by
    have hf (i : I) : f i (cycleMultiply sign z m i) =
        ∑ χ : MulChar (ZMod p) ℂ,
          mellinCoefficient (f i) χ * χ ((cycleMultiply sign z m i : (ZMod p)ˣ) : ZMod p) :=
      (mellin_inversion (f i) _).symm
    simp_rw [hf]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [mulChar_product_apply]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [cycleMultiply, Units.val_mul, map_mul, MulChar.zpow_apply_coe]
    ring
  unfold cycleAverage
  simp_rw [he]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [← Finset.mul_sum, sum_mulChar_units_eq_ite]
  split_ifs
  · field_simp
  · simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_ProductMellinParseval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parseval for the independent moving coordinates on a cycle

The tensor products of unit characters form an orthogonal basis. This
finite identity makes the cycle projection energy a sum of products of
squared Mellin coefficients, with its exact probability normalization.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

attribute [local instance] OAI.Ostmann.productMellinFintype
attribute [local instance] OAI.Ostmann.productMellinDecidableEq
theorem productCharacter_orthogonality {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ σ : I → MulChar (ZMod p) ℂ) :
    (∑ m : I → (ZMod p)ˣ, productCharacter ρ m * conj (productCharacter σ m)) =
      if ρ = σ then (Fintype.card (ZMod p)ˣ : ℂ) ^ Fintype.card I else 0 := by
  classical
  simp only [productCharacter, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (z : (ZMod p)ˣ) => ρ i z * conj (σ i z))]
  simp_rw [mellin_orthogonality]
  by_cases h : ρ = σ
  · subst σ
    simp
  · simp only [h, ite_false, if_false]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, ite_false, if_false]

/-- Probability-normalized Parseval for a finite product of unit groups. -/
theorem product_mellin_synthesis_parseval {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (c : (I → MulChar (ZMod p) ℂ) → ℂ) :
    ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
      (∑ m : I → (ZMod p)ˣ,
        ‖∑ ρ : I → MulChar (ZMod p) ℂ, c ρ * productCharacter ρ m‖ ^ 2) =
      ∑ ρ : I → MulChar (ZMod p) ℂ, ‖c ρ‖ ^ 2 := by
  classical
  let F : (I → (ZMod p)ˣ) → ℂ := fun m => ∑ ρ, c ρ * productCharacter ρ m
  have hc : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ m : I → (ZMod p)ˣ, F m * conj (F m)) =
      (Fintype.card (ZMod p)ˣ : ℂ) ^ Fintype.card I *
        ∑ ρ : I → MulChar (ZMod p) ℂ, c ρ * conj (c ρ) := by
    simp only [F, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.sum_comm]
    calc
      _ = ∑ ρ : I → MulChar (ZMod p) ℂ, c ρ * conj (c σ) *
          ∑ m : I → (ZMod p)ˣ, productCharacter ρ m * conj (productCharacter σ m) := by
        apply Finset.sum_congr rfl
        intro ρ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = _ := by
        simp_rw [productCharacter_orthogonality]
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
        ring
  have hsc : ((Fintype.card (ZMod p)ˣ : ℂ) ^ Fintype.card I)⁻¹ *
      (∑ m : I → (ZMod p)ˣ, F m * conj (F m)) =
        ∑ ρ : I → MulChar (ZMod p) ℂ, c ρ * conj (c ρ) := by
    rw [hs]
    field_simp
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum] at hsc
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_sum, F] using hsc

/-- The projected energy is the sum over the surviving cycle-character tuples. -/
theorem cycleAverage_product_energy {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → (ZMod p)ˣ → ℂ) (sign : I → ℤ) :
    ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
      (∑ m : I → (ZMod p)ˣ, ‖cycleAverage sign (fun m => ∏ i : I, f i (m i)) m‖ ^ 2) =
      ∑ ρ : I → MulChar (ZMod p) ℂ,
        if (∏ i : I, (ρ i) ^ sign i) = 1 then
          ∏ i : I, ‖mellinCoefficient (f i) (ρ i)‖ ^ 2 else 0 := by
  classical
  let c : (I → MulChar (ZMod p) ℂ) → ℂ := fun ρ =>
    if (∏ i : I, (ρ i) ^ sign i) = 1 then ∏ i : I, mellinCoefficient (f i) (ρ i) else 0
  have hexp (m : I → (ZMod p)ˣ) :
      cycleAverage sign (fun m => ∏ i : I, f i (m i)) m =
        ∑ ρ : I → MulChar (ZMod p) ℂ, c ρ * productCharacter ρ m := by
    rw [cycleAverage_product_mellin]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hr : (∏ i : I, (ρ i) ^ sign i) = 1
    · simp only [c, hr, ite_true, if_true, productCharacter, Finset.prod_mul_distrib]
    · simp only [c, hr, ite_false, if_false, zero_mul]
  simp_rw [hexp]
  rw [product_mellin_synthesis_parseval]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hr : (∏ i : I, (ρ i) ^ sign i) = 1
  · simp only [c, hr, ite_true, if_true, norm_prod, Finset.prod_pow]
  · simp only [c, hr, ite_false, if_false, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_SignedCycleBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative coefficient bound for a signed cycle -/

namespace Ostmann

open scoped BigOperators

theorem sum_funSplitAt {I G R : Type*} [Fintype I] [DecidableEq I] [Fintype G]
    [AddCommMonoid R] (i : I) (f : G → ({j : I // j ≠ i} → G) → R) :
    (∑ ρ : I → G, f (ρ i) (fun j => ρ j.1)) =
      ∑ a : G, ∑ τ : {j : I // j ≠ i} → G, f a τ := by
  have h := (Equiv.funSplitAt i G).sum_comp (fun x => f x.1 x.2)
  change (∑ ρ : I → G, f (ρ i) (fun j => ρ j.1)) = _ at h
  simpa only [Fintype.sum_prod_type] using h

/-- Once a cycle index has sign `1` or `-1`, its character is determined by all the others. -/
theorem signedCycleCoefficient_sum_le {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (b : I → G → ℝ) (sign : I → ℤ) (i : I)
    (hi : sign i = 1 ∨ sign i = -1) (S : ℝ)
    (hb : ∀ j a, 0 ≤ b j a) (hS : ∀ a, b i a ≤ S) :
    (∑ ρ : I → G, if (∏ j : I, (ρ j) ^ sign j) = 1 then ∏ j : I, b j (ρ j) else 0) ≤
      S * ∏ j : {j : I // j ≠ i}, ∑ a : G, b j.1 a := by
  classical
  have hproduct (ρ : I → G) :
      (∏ j : I, (ρ j) ^ sign j) = (ρ i) ^ sign i *
        ∏ j : {j : I // j ≠ i}, (ρ j.1) ^ sign j.1 :=
    Fintype.prod_eq_mul_prod_subtype_ne _ i
  have hweight (ρ : I → G) :
      (∏ j : I, b j (ρ j)) = b i (ρ i) * ∏ j : {j : I // j ≠ i}, b j.1 (ρ j.1) :=
    Fintype.prod_eq_mul_prod_subtype_ne _ i
  simp_rw [hproduct, hweight]
  rw [sum_funSplitAt i (fun a τ =>
    if a ^ sign i * (∏ j : {j : I // j ≠ i}, (τ j) ^ sign j.1) = 1 then
      b i a * (∏ j : {j : I // j ≠ i}, b j.1 (τ j)) else 0), Finset.sum_comm]
  have hinner (τ : {j : I // j ≠ i} → G) :
      (∑ a : G, if a ^ sign i * (∏ j, (τ j) ^ sign j.1) = 1 then
        b i a * (∏ j, b j.1 (τ j)) else 0) ≤ S * ∏ j, b j.1 (τ j) := by
    rcases hi with hi | hi
    · simp only [hi, zpow_one, mul_eq_one_iff_eq_inv]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
      exact mul_le_mul_of_nonneg_right (hS _) (Finset.prod_nonneg fun j _ => hb j.1 _)
    · simp only [hi, zpow_neg_one, inv_mul_eq_one]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
      exact mul_le_mul_of_nonneg_right (hS _) (Finset.prod_nonneg fun j _ => hb j.1 _)
  calc
    _ ≤ ∑ τ : {j : I // j ≠ i} → G, S * ∏ j, b j.1 (τ j) :=
      Finset.sum_le_sum fun τ _ => hinner τ
    _ = _ := by rw [← Finset.mul_sum, Fintype.prod_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_HeldCycleAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent held-leaf averaging in the cycle projection -/

namespace Ostmann

open scoped BigOperators

theorem uniform_product_average {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]
    (f : I → H → ℝ) :
    ((Fintype.card H : ℝ) ^ Fintype.card I)⁻¹ * (∑ h : I → H, ∏ i : I, f i (h i)) =
      ∏ i : I, (Fintype.card H : ℝ)⁻¹ * ∑ h : H, f i h := by
  rw [← Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, inv_pow]

attribute [local instance] OAI.Ostmann.heldCycleFintype
attribute [local instance] OAI.Ostmann.heldCycleDecidableEq
/-- Fubini and the cycle-character relation remain exact after exposing the
independent held coordinates in every affected quartet. -/
theorem held_cycle_product_energy {p : ℕ} [Fact p.Prime]
    {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]
    (f : I → H → (ZMod p)ˣ → ℂ) (sign : I → ℤ) :
    ((Fintype.card H : ℝ) ^ Fintype.card I)⁻¹ * (∑ h : I → H,
      ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
        ∑ m : I → (ZMod p)ˣ,
          ‖cycleAverage sign (fun m => ∏ i : I, f i (h i) (m i)) m‖ ^ 2) =
    ∑ ρ : I → MulChar (ZMod p) ℂ,
      if (∏ i : I, (ρ i) ^ sign i) = 1 then
        ∏ i : I, (Fintype.card H : ℝ)⁻¹ * ∑ h : H, ‖mellinCoefficient (f i h) (ρ i)‖ ^ 2
      else 0 := by
  classical
  simp_rw [cycleAverage_product_energy]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hr : (∏ i : I, (ρ i) ^ sign i) = 1
  · simp only [hr, ite_true, if_true]
    rw [← Finset.mul_sum]
    simpa only [Finset.mul_sum] using
      uniform_product_average (fun i h => ‖mellinCoefficient (f i h) (ρ i)‖ ^ 2)
  · simp only [hr, ite_false, if_false, mul_zero, Finset.sum_const_zero]

theorem held_cycle_product_energy_le {p : ℕ} [Fact p.Prime]
    {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]
    (f : I → H → (ZMod p)ˣ → ℂ) (sign : I → ℤ)
    (B : I → MulChar (ZMod p) ℂ → ℝ)
    (hcoeff : ∀ i χ, (Fintype.card H : ℝ)⁻¹ *
      (∑ h : H, ‖mellinCoefficient (f i h) χ‖ ^ 2) ≤ B i χ) :
    ((Fintype.card H : ℝ) ^ Fintype.card I)⁻¹ * (∑ h : I → H,
      ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
        ∑ m : I → (ZMod p)ˣ,
          ‖cycleAverage sign (fun m => ∏ i : I, f i (h i) (m i)) m‖ ^ 2) ≤
    ∑ ρ : I → MulChar (ZMod p) ℂ,
      if (∏ i : I, (ρ i) ^ sign i) = 1 then ∏ i : I, B i (ρ i) else 0 := by
  classical
  rw [held_cycle_product_energy]
  apply Finset.sum_le_sum
  intro ρ _
  split_ifs
  · exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hcoeff i (ρ i))
  · exact le_rfl

/-- Averaging independent quartet arguments factorizes each surviving
character term before a single character is eliminated by the cycle. -/
theorem cycle_majorant_average {I G Y : Type*} [Fintype I] [DecidableEq I] [Fintype G] [Fintype Y]
    [CommGroup G] [DecidableEq G] (B : I → G → Y → ℝ) (sign : I → ℤ) :
    ((Fintype.card Y : ℝ) ^ Fintype.card I)⁻¹ * (∑ y : I → Y,
      ∑ ρ : I → G, if (∏ i : I, (ρ i) ^ sign i) = 1 then ∏ i : I, B i (ρ i) (y i) else 0) =
    ∑ ρ : I → G, if (∏ i : I, (ρ i) ^ sign i) = 1 then
      ∏ i : I, (Fintype.card Y : ℝ)⁻¹ * ∑ y : Y, B i (ρ i) y else 0 := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hr : (∏ i : I, (ρ i) ^ sign i) = 1
  · simp only [hr, ite_true, if_true]
    rw [← Finset.mul_sum]
    simpa only [Finset.mul_sum] using uniform_product_average (fun i y => B i (ρ i) y)
  · simp only [hr, ite_false, if_false, mul_zero, Finset.sum_const_zero]

theorem cycle_majorant_average_le {I G Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype G] [Fintype Y] [CommGroup G] [DecidableEq G]
    (B : I → G → Y → ℝ) (sign : I → ℤ) (i : I) (hi : sign i = 1 ∨ sign i = -1)
    (M : ℝ) (H : I → ℝ) (hM : 0 ≤ M)
    (hB : ∀ j χ y, 0 ≤ B j χ y)
    (hsmall : ∀ χ, (Fintype.card Y : ℝ)⁻¹ * ∑ y : Y, B i χ y ≤ M)
    (hmass : ∀ j, (∑ χ : G, (Fintype.card Y : ℝ)⁻¹ * ∑ y : Y, B j χ y) ≤ H j) :
    ((Fintype.card Y : ℝ) ^ Fintype.card I)⁻¹ * (∑ y : I → Y,
      ∑ ρ : I → G, if (∏ j : I, (ρ j) ^ sign j) = 1 then ∏ j : I, B j (ρ j) (y j) else 0) ≤
      M * ∏ j : {j : I // j ≠ i}, H j.1 := by
  classical
  rw [cycle_majorant_average]
  apply (signedCycleCoefficient_sum_le
    (fun j χ => (Fintype.card Y : ℝ)⁻¹ * ∑ y : Y, B j χ y) sign i hi M
    (fun j χ => mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hB j χ y)) hsmall).trans
  apply mul_le_mul_of_nonneg_left _ hM
  exact Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun χ _ =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => hB j.1 χ y)) (fun j _ => hmass j.1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProductFibers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent product fibers at the bottom quartet level -/

namespace Ostmann

open scoped BigOperators

theorem quartetProductFiberEquiv_symm {U : Type*} [CommGroup U] (n : ℕ)
    (P : TreeLeafIndex n → U) (m : (i : TreeLeafIndex n) → TreeLeafFiber U 2 (P i))
    (i : TreeLeafIndex n) :
    quartetBlockEquiv U n ((quartetProductFiberEquiv n P).symm m).1 i = (m i).1 := by
  exact congrFun ((quartetBlockEquiv U n).apply_symm_apply (fun i => (m i).1)) i

theorem card_quartetProductFiber {U : Type*} [CommGroup U] [Fintype U]
    (n : ℕ) (P : TreeLeafIndex n → U) :
    Fintype.card (QuartetProductFiber U n P) = (Fintype.card U ^ 3) ^ (2 ^ n) := by
  rw [Fintype.card_congr (quartetProductFiberEquiv n P), Fintype.card_pi]
  simp only [card_treeLeafFiber, Nat.reducePow, Nat.reduceSub, Finset.prod_const,
    Finset.card_univ, card_treeLeafIndex]

theorem sum_treeLeafTuple_by_quartetProducts {U R : Type*} [CommGroup U] [Fintype U]
    [AddCommMonoid R] (n : ℕ) (f : TreeLeafTuple U (n + 2) → R) :
    (∑ m : TreeLeafTuple U (n + 2), f m) =
      ∑ P : TreeLeafIndex n → U, ∑ m : QuartetProductFiber U n P, f m.1 := by
  classical
  have h := (Equiv.sigmaFiberEquiv (quartetProducts (U := U) n)).sum_comp f
  change (∑ m : (Σ P : TreeLeafIndex n → U, QuartetProductFiber U n P), f m.2.1) = _ at h
  simpa only [Fintype.sum_sigma] using h.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeProfile
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonuniform nonnegative weights at a horizontal level of the tree -/

namespace Ostmann

open scoped BigOperators

theorem treeProfileMajorant_zero {p : ℕ} [Fact p.Prime]
    (n : ℕ) (w : TreeLeafTuple (ZMod p → ℝ) n) : treeProfileMajorant n w 0 = 0 := by
  cases n <;> simp [treeProfileMajorant]

theorem treeProfileMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (n : ℕ) (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w)
    (d : ZMod p) : 0 ≤ treeProfileMajorant n w d := by
  induction n generalizing d with
  | zero =>
    simp only [treeProfileMajorant]
    split_ifs
    · exact le_rfl
    · exact hw d
  | succ n ih =>
    simp only [treeProfileMajorant]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by positivity)
        (differenceMoment_nonneg _ _ (ih w.1 hw.1) (ih w.2 hw.2) d)

theorem treeProfileMean_nonneg {p : ℕ} [Fact p.Prime]
    (n : ℕ) (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w) :
    0 ≤ treeProfileMean n w := by
  induction n with
  | zero => exact div_nonneg (Finset.sum_nonneg fun x _ => hw x) (Nat.cast_nonneg _)
  | succ n ih => exact mul_nonneg (ih w.1 hw.1) (ih w.2 hw.2)

/-- The density loss is two for every internal node, with a separate mean for each leaf. -/
theorem treeProfileMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (n : ℕ) (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w) :
    (∑ d : (ZMod p)ˣ, treeProfileMajorant n w d) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤
        (2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w := by
  induction n with
  | zero => simp [treeProfileMajorant, treeProfileMean, Units.ne_zero]
  | succ n ih =>
    have hU : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hL := ih w.1 hw.1
    have hR := ih w.2 hw.2
    have hzL := sum_units_eq_sum_of_zero _ (treeProfileMajorant_zero n w.1)
    have hzR := sum_units_eq_sum_of_zero _ (treeProfileMajorant_zero n w.2)
    have hnL : 0 ≤ (∑ d : (ZMod p)ˣ, treeProfileMajorant n w.1 d) /
        (Fintype.card (ZMod p)ˣ : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun d _ => treeProfileMajorant_nonneg n w.1 hw.1 d) hU.le
    have hnR : 0 ≤ (2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w.2 :=
      mul_nonneg (by positivity) (treeProfileMean_nonneg n w.2 hw.2)
    calc
      _ = (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
          (∑ d : (ZMod p)ˣ,
            differenceMoment (treeProfileMajorant n w.1) (treeProfileMajorant n w.2) d) /
              (Fintype.card (ZMod p)ˣ : ℝ) := by
        simp only [treeProfileMajorant, Units.ne_zero, ite_false, if_false, ← Finset.mul_sum]
      _ ≤ (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
          ((∑ x : ZMod p, treeProfileMajorant n w.1 x) *
            ∑ x : ZMod p, treeProfileMajorant n w.2 x) /
              (Fintype.card (ZMod p)ˣ : ℝ) := by
        apply div_le_div_of_nonneg_right _ hU.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_units_differenceMoment_le _ _
          (treeProfileMajorant_nonneg n w.1 hw.1) (treeProfileMajorant_nonneg n w.2 hw.2)
      _ = 2 * (((∑ d : (ZMod p)ˣ, treeProfileMajorant n w.1 d) /
          (Fintype.card (ZMod p)ˣ : ℝ)) *
          ((∑ d : (ZMod p)ˣ, treeProfileMajorant n w.2 d) /
          (Fintype.card (ZMod p)ˣ : ℝ))) := by rw [← hzL, ← hzR]; ring
      _ ≤ 2 * (((2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w.1) *
          ((2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w.2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hL hR
          (div_nonneg (Finset.sum_nonneg fun d _ =>
            treeProfileMajorant_nonneg n w.2 hw.2 d) hU.le)
          (mul_nonneg (by positivity) (treeProfileMean_nonneg n w.1 hw.1))) (by norm_num)
      _ = _ := by
        have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
        have he : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + (2 ^ n - 1) + 1 := by
          rw [pow_succ]; omega
        rw [he, pow_add, pow_add]
        simp only [treeProfileMean, pow_one]
        ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTreeProfile
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual rational tree with different weights at a horizontal level -/

namespace Ostmann

open scoped BigOperators

theorem rationalProfileMoment_nonneg {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w)
    (XL XR P : (ZMod p)ˣ) : 0 ≤ rationalProfileMoment D T w XL XR P := by
  induction T generalizing XL XR P with
  | leaf s C => exact hw _
  | node s CL CR u left right ihL ihR =>
    simp only [rationalProfileMoment]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro m _
    dsimp
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (ihL w.1 hw.1 _ _ _) (ihR w.2 hw.2 _ _ _)

theorem rationalProfileMoment_le_majorant {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w)
    (XL XR P : (ZMod p)ˣ) :
    rationalProfileMoment D T w XL XR P ≤
      treeProfileMajorant n w (rationalTreeArgument T.frequency C D XL XR P) := by
  induction T generalizing XL XR P with
  | leaf s C =>
    simp only [rationalProfileMoment, RationalTreeData.frequency, treeProfileMajorant,
      Units.ne_zero, ite_false, if_false, le_refl]
  | @node n s CL CR u left right ihL ihR =>
    have harg := rationalTreeArgument_node s CL CR D XL XR P
    change _ ≤ treeProfileMajorant (n + 1) w (rationalTreeArgument s (CL * CR) D XL XR P)
    rw [harg]
    simp only [treeProfileMajorant, Units.ne_zero, ite_false, if_false]
    calc
      _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ m : (ZMod p)ˣ, rationalNodeValue s left.frequency right.frequency D u XL XR CL CR P
            (treeProfileMajorant n w.1) (treeProfileMajorant n w.2) m := by
        unfold rationalProfileMoment
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro m _
        dsimp [rationalNodeValue]
        split_ifs with hv
        · exact le_rfl
        · have hL := ihL w.1 hw.1 (Units.mk0 _ hv) XL m
          have hR := ihR w.2 hw.2 (Units.mk0 _ hv) XR (P / m)
          rw [rationalTreeArgument_child] at hL hR
          exact mul_le_mul hL hR (rationalProfileMoment_nonneg D right w.2 hw.2 _ _ _)
            (treeProfileMajorant_nonneg n w.1 hw.1 _)
      _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          (2 * ∑ x : ZMod p, treeProfileMajorant n w.1 x *
            treeProfileMajorant n w.2 (x - rationalNodeArgument s D XL XR CL CR P)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact rationalNodeValue_sum_le s left.frequency right.frequency D u XL XR CL CR P
          _ _ (treeProfileMajorant_zero n w.1) (treeProfileMajorant_zero n w.2)
          (treeProfileMajorant_nonneg n w.1 hw.1) (treeProfileMajorant_nonneg n w.2 hw.2)
      _ = _ := by unfold differenceMoment; ring

theorem rationalProfileMoment_mean_le {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w)
    (XL XR : (ZMod p)ˣ) :
    (∑ P : (ZMod p)ˣ, rationalProfileMoment D T w XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ (2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w := by
  calc
    _ ≤ (∑ P : (ZMod p)ˣ,
        treeProfileMajorant n w (rationalTreeArgument T.frequency C D XL XR P)) /
          (Fintype.card (ZMod p)ˣ : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun P _ => rationalProfileMoment_le_majorant D T w hw XL XR P
    _ = (∑ d : (ZMod p)ˣ, treeProfileMajorant n w d) /
          (Fintype.card (ZMod p)ˣ : ℝ) := by
      congr 1
      exact (rationalTreeArgumentEquiv T.frequency C D XL XR).sum_comp
        (fun d => treeProfileMajorant n w d)
    _ ≤ _ := treeProfileMajorant_mean_le n w hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalProfileLeaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted horizontal-level averages with actual independent leaf products -/

namespace Ostmann

open scoped BigOperators

theorem rationalProfileLeafValue_fiber_sum {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (XL XR P : (ZMod p)ˣ) :
    (∑ x : TreeLeafFiber (ZMod p)ˣ n P, rationalProfileLeafValue D T w XL XR x.1) =
      (Fintype.card (ZMod p)ˣ : ℝ) ^ (2 ^ n - 1) * rationalProfileMoment D T w XL XR P := by
  induction T generalizing XL XR P with
  | leaf s C =>
    have he : ∀ x : TreeLeafFiber (ZMod p)ˣ 0 P, (x.1 : (ZMod p)ˣ) = P :=
      fun x => x.property
    simp only [rationalProfileLeafValue, he, Finset.sum_const, Finset.card_univ,
      card_treeLeafFiber, pow_zero, Nat.sub_self, pow_zero, one_smul, one_mul,
      rationalProfileMoment]
  | @node n s CL CR u left right ihL ihR =>
    rw [sum_treeLeafFiber_succ]
    have hterm (m : (ZMod p)ˣ) :
        (∑ a : TreeLeafFiber (ZMod p)ˣ n m,
          ∑ b : TreeLeafFiber (ZMod p)ˣ n (P / m),
            rationalProfileLeafValue D (.node s CL CR u left right) w XL XR (a.1, b.1)) =
        ((Fintype.card (ZMod p)ˣ : ℝ) ^ (2 ^ n - 1)) ^ 2 *
          (let HL : (ZMod p)ˣ := XL * CL * m
           let HR : (ZMod p)ˣ := XR * CR * (P / m)
           let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
           if hv : v = 0 then 0 else
             rationalProfileMoment D left w.1 (Units.mk0 v hv) XL m *
               rationalProfileMoment D right w.2 (Units.mk0 v hv) XR (P / m)) := by
      have hfib {Q : (ZMod p)ˣ} (x : TreeLeafFiber (ZMod p)ˣ n Q) :
          treeLeafProduct n x.1 = Q := x.property
      simp only [rationalProfileLeafValue, hfib]
      dsimp
      split_ifs with hv
      · simp
      · let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u
          ((XL : ZMod p) * CL * m) ((XR : ZMod p) * CR * (P / m : (ZMod p)ˣ))
        let V : (ZMod p)ˣ := Units.mk0 v hv
        change (∑ a : TreeLeafFiber (ZMod p)ˣ n m,
          ∑ b : TreeLeafFiber (ZMod p)ˣ n (P / m),
            rationalProfileLeafValue D left w.1 V XL a.1 *
            rationalProfileLeafValue D right w.2 V XR b.1) = _
        rw [← Fintype.sum_mul_sum
          (fun a : TreeLeafFiber (ZMod p)ˣ n m => rationalProfileLeafValue D left w.1 V XL a.1)
          (fun b : TreeLeafFiber (ZMod p)ˣ n (P / m) => rationalProfileLeafValue D right w.2 V XR b.1)]
        rw [ihL, ihR]
        ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    simp only [rationalProfileMoment]
    have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    have hexp : 2 ^ (n + 1) - 1 = (2 ^ n - 1) * 2 + 1 := by
      rw [pow_succ]
      omega
    rw [hexp]
    conv_rhs => arg 1; rw [pow_succ, pow_mul]
    field_simp

theorem rationalProfileLeafValue_mean_eq {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (XL XR : (ZMod p)ˣ) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n, rationalProfileLeafValue D T w XL XR x) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) =
    (∑ P : (ZMod p)ˣ, rationalProfileMoment D T w XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) := by
  rw [sum_treeLeafTuple_by_product]
  simp_rw [rationalProfileLeafValue_fiber_sum]
  rw [← Finset.mul_sum, card_treeLeafTuple, Nat.cast_pow]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  conv_lhs => rhs; rw [← Nat.sub_add_cancel hn, pow_succ]
  field_simp

/-- Horizontal-level domination for a different nonnegative test at each node. -/
theorem rationalProfileLeafValue_mean_le {p : ℕ} [Fact p.Prime] (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w)
    (XL XR : (ZMod p)ˣ) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n, rationalProfileLeafValue D T w XL XR x) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤
        (2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w := by
  rw [rationalProfileLeafValue_mean_eq]
  exact rationalProfileMoment_mean_le D T w hw XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalQuartetCut
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutting an actual rational tree at its bottom quartets

The option-valued state records ancestor validity. On a valid cut each
state contains the original depth-two tree and its propagated current
entries. No quartet replacement or independence hypothesis is used.
-/

namespace Ostmann

open scoped BigOperators

theorem treeLeafProduct_quartetBlocks {U : Type*} [CommGroup U] (n : ℕ)
    (m : TreeLeafTuple U (n + 2)) :
    treeLeafProduct (n + 2) m = treeLeafProduct n
      (treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv U n m)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change treeLeafProduct (n + 2) m.1 * treeLeafProduct (n + 2) m.2 = _
    rw [ih m.1, ih m.2]
    rfl

theorem quartetCutValue_pair {A B R : Type*} [MulZeroClass R] (f : A → B → R)
    (n : ℕ) (L R' : Option (TreeLeafTuple A n)) (b : TreeLeafTuple B (n + 1)) :
    quartetCutValue f (n + 1) (do let l ← L; let r ← R'; pure (l, r)) b =
      quartetCutValue f n L b.1 * quartetCutValue f n R' b.2 := by
  cases L <;> cases R' <;> simp [quartetCutValue, treeLeafZipProduct]

/-- Holding all bottom-quartet products fixes the entire upper recursion. -/
theorem rationalTreeAmplitude_cut {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (m : TreeLeafTuple (ZMod p)ˣ (n + 2)) :
    rationalTreeAmplitude g D T XL XR c m =
      quartetCutValue (rationalQuartetStateAmplitude g D) n
        (rationalQuartetStates n T XL XR c
          (treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv (ZMod p)ˣ n m)))
        (quartetBlockTupleEquiv (ZMod p)ˣ n m) := by
  induction n generalizing C XL XR with
  | zero => rfl
  | succ n ih =>
    cases T with
    | node s CL CR u left right =>
      change rationalTreeAmplitude g D (.node s CL CR u left right) XL XR c m =
        quartetCutValue (rationalQuartetStateAmplitude g D) (n + 1)
          (rationalQuartetStates (n + 1) (.node s CL CR u left right) XL XR c
            (treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv (ZMod p)ˣ n m.1),
             treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv (ZMod p)ˣ n m.2)))
          (quartetBlockTupleEquiv (ZMod p)ˣ n m.1, quartetBlockTupleEquiv (ZMod p)ˣ n m.2)
      simp only [rationalTreeAmplitude, rationalQuartetStates]
      simp only [treeLeafProduct_quartetBlocks n m.1, treeLeafProduct_quartetBlocks n m.2]
      split_ifs with hv
      · rfl
      · rw [quartetCutValue_pair]
        exact congrArg₂ (· * ·) (ih left _ _ c.1 m.1) (ih right _ _ c.2 m.2)

/-- The weighted arguments exposed at the cut are exactly the leaves of
the truncated rational tree, with the same invalid-ancestor zeros. -/
theorem rationalQuartetStates_profile {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafTuple (ZMod p)ˣ n)
    (w : TreeLeafTuple (ZMod p → ℝ) n) :
    quartetCutValue (fun S (wp : (ZMod p → ℝ) × (ZMod p)ˣ) =>
        wp.1 (rationalQuartetStateArgument D S wp.2)) n
      (rationalQuartetStates n T XL XR c P) (treeLeafZip n w P) =
      rationalProfileLeafValue D (T.cutTwo n) w XL XR P := by
  induction n generalizing C XL XR with
  | zero => rfl
  | succ n ih =>
    cases T with
    | node s CL CR u left right =>
      simp only [rationalQuartetStates, RationalTreeData.cutTwo, rationalProfileLeafValue,
        RationalTreeData.frequency_cutTwo, treeLeafZip]
      split_ifs with hv
      · rfl
      · rw [quartetCutValue_pair]
        exact congrArg₂ (· * ·) (ih left _ _ c.1 P.1 w.1) (ih right _ _ c.2 P.2 w.2)

/-- Horizontal density domination applies directly to the genuine cut
states, even though their current entries depend on the product vector. -/
theorem rationalQuartetStates_profile_mean_le {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2))
    (w : TreeLeafTuple (ZMod p → ℝ) n) (hw : treeWeightsNonneg n w) :
    (∑ P : TreeLeafTuple (ZMod p)ˣ n,
      quartetCutValue (fun S (wp : (ZMod p → ℝ) × (ZMod p)ˣ) =>
        wp.1 (rationalQuartetStateArgument D S wp.2)) n
        (rationalQuartetStates n T XL XR c P) (treeLeafZip n w P)) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤
        (2 : ℝ) ^ (2 ^ n - 1) * treeProfileMean n w := by
  simp_rw [rationalQuartetStates_profile]
  exact rationalProfileLeafValue_mean_le D (T.cutTwo n) w hw XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeTupleProfiles
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Indexed products and means at a horizontal tree level -/

namespace Ostmann

open scoped BigOperators

theorem treeLeafZipProduct_eq_prod {A B R : Type*} [CommMonoid R]
    (f : A → B → R) (n : ℕ) (a : TreeLeafTuple A n) (b : TreeLeafTuple B n) :
    treeLeafZipProduct f n a b =
      ∏ i : TreeLeafIndex n, f (treeLeafTupleEquiv A n a i) (treeLeafTupleEquiv B n b i) := by
  induction n with
  | zero =>
    change f a b = ∏ _ : Unit, f a b
    simp
  | succ n ih =>
    change treeLeafZipProduct f n a.1 b.1 * treeLeafZipProduct f n a.2 b.2 =
      ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n,
        f (treeLeafTupleEquiv A (n + 1) a i) (treeLeafTupleEquiv B (n + 1) b i)
    rw [Fintype.prod_sum_type, ih, ih]
    rfl

theorem treeWeightsNonneg_iff {p : ℕ} (n : ℕ)
    (w : TreeLeafTuple (ZMod p → ℝ) n) :
    treeWeightsNonneg n w ↔ ∀ i : TreeLeafIndex n, ∀ x, 0 ≤ treeLeafTupleEquiv _ n w i x := by
  induction n with
  | zero =>
    constructor
    · intro h _ x; exact h x
    · intro h x; exact h () x
  | succ n ih =>
    constructor
    · intro h i x
      cases i with
      | inl i => exact (ih w.1).mp h.1 i x
      | inr i => exact (ih w.2).mp h.2 i x
    · intro h
      exact ⟨(ih w.1).mpr (fun i x => h (.inl i) x),
        (ih w.2).mpr (fun i x => h (.inr i) x)⟩

theorem treeProfileMean_eq_prod {p : ℕ} [Fact p.Prime] (n : ℕ)
    (w : TreeLeafTuple (ZMod p → ℝ) n) :
    treeProfileMean n w = ∏ i : TreeLeafIndex n,
      (∑ x : (ZMod p)ˣ, treeLeafTupleEquiv _ n w i x) / (Fintype.card (ZMod p)ˣ : ℝ) := by
  induction n with
  | zero =>
    change (∑ x : (ZMod p)ˣ, w x) / (Fintype.card (ZMod p)ˣ : ℝ) =
      ∏ _ : Unit, (∑ x : (ZMod p)ˣ, w x) / (Fintype.card (ZMod p)ˣ : ℝ)
    simp
  | succ n ih =>
    change treeProfileMean n w.1 * treeProfileMean n w.2 =
      ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n,
        (∑ x : (ZMod p)ˣ, treeLeafTupleEquiv _ (n + 1) w i x) /
          (Fintype.card (ZMod p)ˣ : ℝ)
    rw [Fintype.prod_sum_type, ih, ih]
    rfl

theorem quartetProducts_eq_map {U : Type*} [CommGroup U] (n : ℕ)
    (m : TreeLeafTuple U (n + 2)) :
    quartetProducts n m = treeLeafTupleEquiv U n
      (treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv U n m)) := by
  funext i
  exact (treeLeafTupleEquiv_map (treeLeafProduct 2) n (quartetBlockTupleEquiv U n m) i).symm

theorem rationalTreeAmplitude_product_of_cut {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S)
    (m : QuartetProductFiber (ZMod p)ˣ n P) :
    rationalTreeAmplitude g D T XL XR c m.1 = ∏ i : TreeLeafIndex n,
      rationalQuartetStateAmplitude g D (treeLeafTupleEquiv _ n S i)
        (quartetBlockEquiv (ZMod p)ˣ n m.1 i) := by
  have hP : treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv (ZMod p)ˣ n m.1) =
      (treeLeafTupleEquiv _ n).symm P := by
    apply (treeLeafTupleEquiv _ n).injective
    rw [Equiv.apply_symm_apply, ← quartetProducts_eq_map]
    exact m.property
  rw [rationalTreeAmplitude_cut, hP, hS]
  exact treeLeafZipProduct_eq_prod _ n S _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetHorizontalMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the surviving characters after horizontal density domination -/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.horizontalCharFintype
/-- Apply horizontal density first, then eliminate one surviving character.
The majorants may vary with the quartet label but not with ancestor data. -/
theorem rationalCutCharacterSum_mean_le {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2))
    (B : TreeLeafIndex n → MulChar (ZMod p) ℂ → ZMod p → ℝ)
    (sign : TreeLeafIndex n → ℤ) (i : TreeLeafIndex n)
    (hi : sign i = 1 ∨ sign i = -1) (M H : ℝ) (hM : 0 ≤ M)
    (hB : ∀ j χ y, 0 ≤ B j χ y)
    (hsmall : ∀ χ, (∑ y : (ZMod p)ˣ, B i χ y) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ M)
    (hmass : ∀ j, (∑ χ : MulChar (ZMod p) ℂ,
      (∑ y : (ZMod p)ˣ, B j χ y) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤ H) :
    (∑ P : TreeLeafTuple (ZMod p)ˣ n, rationalCutCharacterSum D n T XL XR c B sign P) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤
      (2 : ℝ) ^ (2 ^ n - 1) * (M * H ^ (2 ^ n - 1)) := by
  classical
  let w (ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ) : TreeLeafTuple (ZMod p → ℝ) n :=
    (treeLeafTupleEquiv _ n).symm (fun i => B i (ρ i))
  let F (ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ) (P : TreeLeafTuple (ZMod p)ˣ n) :=
    quartetCutValue (fun S (wp : (ZMod p → ℝ) × (ZMod p)ˣ) =>
      wp.1 (rationalQuartetStateArgument D S wp.2)) n
      (rationalQuartetStates n T XL XR c P) (treeLeafZip n (w ρ) P)
  have hp (ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ) :
      (∑ P : TreeLeafTuple (ZMod p)ˣ n, F ρ P) /
        (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤
        (2 : ℝ) ^ (2 ^ n - 1) * ∏ j : TreeLeafIndex n,
          (∑ y : (ZMod p)ˣ, B j (ρ j) y) / (Fintype.card (ZMod p)ˣ : ℝ) := by
    have hw : treeWeightsNonneg n (w ρ) := by
      rw [treeWeightsNonneg_iff]
      intro j y
      simpa only [w, Equiv.apply_symm_apply] using hB j (ρ j) y
    have h := rationalQuartetStates_profile_mean_le D n T XL XR c (w ρ) hw
    rw [treeProfileMean_eq_prod] at h
    simpa only [w, Equiv.apply_symm_apply] using h
  have hc := cycle_majorant_average_le (fun j χ (y : (ZMod p)ˣ) => B j χ y)
    sign i hi M (fun _ => H) hM (fun j χ y => hB j χ y)
    (fun χ => by simpa only [div_eq_mul_inv, mul_comm] using hsmall χ)
    (fun j => by simpa only [div_eq_mul_inv, mul_comm] using hmass j)
  rw [cycle_majorant_average (fun j χ (y : (ZMod p)ˣ) => B j χ y) sign] at hc
  have hcard : Fintype.card {j : TreeLeafIndex n // j ≠ i} = 2 ^ n - 1 := by
    simpa only [Fintype.card_subtype_eq, card_treeLeafIndex] using
      Fintype.card_subtype_compl (fun j : TreeLeafIndex n => j = i)
  have hchars : (∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
      if (∏ j : TreeLeafIndex n, (ρ j) ^ sign j) = 1 then
        ∏ j : TreeLeafIndex n,
          (∑ y : (ZMod p)ˣ, B j (ρ j) y) / (Fintype.card (ZMod p)ˣ : ℝ) else 0) ≤
      M * H ^ (2 ^ n - 1) := by
    simpa only [Finset.prod_const, Finset.card_univ, hcard, div_eq_mul_inv, mul_comm] using hc
  calc
    _ = ∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
        if (∏ j : TreeLeafIndex n, (ρ j) ^ sign j) = 1 then
          (∑ P : TreeLeafTuple (ZMod p)ˣ n, F ρ P) /
            (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) else 0 := by
      unfold rationalCutCharacterSum
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ρ _
      split_ifs
      · rfl
      · simp
    _ ≤ (2 : ℝ) ^ (2 ^ n - 1) *
        ∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
          if (∏ j : TreeLeafIndex n, (ρ j) ^ sign j) = 1 then
            ∏ j : TreeLeafIndex n,
              (∑ y : (ZMod p)ˣ, B j (ρ j) y) / (Fintype.card (ZMod p)ˣ : ℝ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ρ _
      split_ifs
      · exact hp ρ
      · simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hchars (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetCutConjugations
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A horizontal cut preserves the original sibling conjugations -/

namespace Ostmann

theorem rationalQuartetStates_conjugations {p : ℕ} [Fact p.Prime]
    (n : ℕ) {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ (n + 2) C)
    (XL XR : (ZMod p)ˣ) (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafTuple (ZMod p)ˣ n)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c P = some S) :
    treeLeafMap RationalQuartetState.conjugations n S = quartetBlockTupleEquiv Bool n c := by
  induction n generalizing C XL XR with
  | zero =>
    have h := Option.some.inj hS
    cases h
    rfl
  | succ n ih =>
    cases T with
    | node s CL CR u left right =>
      simp only [rationalQuartetStates] at hS
      split_ifs at hS with hv
      let V : (ZMod p)ˣ := Units.mk0
          (reconstructedEntry (s : ZMod p) left.frequency right.frequency u
            (XL * CL * treeLeafProduct n P.1) (XR * CR * treeLeafProduct n P.2)) hv
      change (do
        let L ← rationalQuartetStates n left V XL c.1 P.1
        let R ← rationalQuartetStates n right V XR c.2 P.2
        pure (L, R)) = some S at hS
      cases hL : rationalQuartetStates n left V XL c.1 P.1 with
      | none => simp [hL] at hS
      | some L =>
        cases hR : rationalQuartetStates n right V XR c.2 P.2 with
        | none => simp [hL, hR] at hS
        | some R =>
          have he : (L, R) = S := by simpa [hL, hR] using hS
          subst S
          exact Prod.ext (ih left V XL c.1 P.1 L hL) (ih right V XR c.2 P.2 R hR)

theorem rationalQuartetStates_conjugations_at {p : ℕ} [Fact p.Prime]
    (n : ℕ) {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ (n + 2) C)
    (XL XR : (ZMod p)ˣ) (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafTuple (ZMod p)ˣ n)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c P = some S) (i : TreeLeafIndex n) :
    (treeLeafTupleEquiv _ n S i).conjugations = quartetBlockEquiv Bool n c i := by
  have h := congrArg (fun s => treeLeafTupleEquiv _ n s i)
    (rationalQuartetStates_conjugations n T XL XR c P S hS)
  simpa only [treeLeafTupleEquiv_map, quartetBlockEquiv, Equiv.trans_apply] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetIndexCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf coordinates within a labeled bottom quartet -/

namespace Ostmann

open scoped BigOperators

theorem quartetBlockEquiv_read (A : Type*) (n : ℕ) (m : TreeLeafTuple A (n + 2))
    (q : TreeLeafIndex n) (j : TreeLeafIndex 2) :
    treeLeafTupleEquiv A 2 (quartetBlockEquiv A n m q) j =
      treeLeafTupleEquiv A (n + 2) m (quartetLeafIndex n q j) := by
  induction n with
  | zero => cases q; rfl
  | succ n ih =>
    cases q with
    | inl q => exact ih m.1 q
    | inr q => exact ih m.2 q

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetTestSymmetries
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reflection and conjugation preserve the hypotheses for every local row -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem orientedPairBase_zero {p : ℕ} (g : ZMod p → ℂ) (hg : g 0 = 0) (friendly : Bool) :
    orientedPairBase g friendly 0 = 0 := by
  cases friendly <;> simp [orientedPairBase, hg]

theorem orientedPairBase_energy {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (friendly : Bool) :
    (∑ x : ZMod p, ‖orientedPairBase g friendly x‖ ^ 2) = ∑ x : ZMod p, ‖g x‖ ^ 2 := by
  cases friendly
  · simp only [orientedPairBase, Bool.false_eq_true, ite_false, if_false, Complex.norm_conj]
    exact (Equiv.neg (ZMod p)).bijective.sum_comp (fun x => ‖g x‖ ^ 2)
  · rfl

theorem MixedFourierBound.orientedPairBase {p : ℕ} [Fact p.Prime]
    {g : ZMod p → ℂ} {ε : ℝ} (hg : MixedFourierBound g ε) (friendly : Bool) :
    MixedFourierBound (orientedPairBase g friendly) ε := by
  cases friendly
  · simpa only [Ostmann.orientedPairBase, Bool.false_eq_true, ite_false, if_false,
      Units.val_neg, Units.val_one, neg_one_mul] using hg.conj.unit_mul (-1)
  · exact hg

theorem sum_units_neg {p : ℕ} [Fact p.Prime] (f : ZMod p → ℝ) :
    (∑ y : (ZMod p)ˣ, f (-(y : ZMod p))) = ∑ y : (ZMod p)ˣ, f y := by
  simpa only [Equiv.neg_apply, Units.val_neg] using
    (Equiv.neg (ZMod p)ˣ).bijective.sum_comp (fun y => f y)

theorem conjugated_crossPairMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (cL cR left right : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ,
      crossPairMajorant (orientedPairBase (pairConjugate g cL) left)
        (orientedPairBase (pairConjugate g cR) right) left right ρ y) /
          (Fintype.card (ZMod p)ˣ : ℝ) ≤
      2 * (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) *
        (friendlyQuartetError p ε + twoBadQuartetError p ε)) := by
  have he (c friendly : Bool) :
      (∑ x : ZMod p, ‖orientedPairBase (pairConjugate g c) friendly x‖ ^ 2) ≤ (p : ℝ) := by
    rw [orientedPairBase_energy]
    simpa only [norm_pairConjugate] using henergy
  apply crossPairMajorant_mean_le _ _ left right _
    (add_nonneg (friendlyQuartetError_nonneg p ε) (twoBadQuartetError_nonneg p ε))
  intro ν
  exact concrete_quartet_fourier_le _ _
    (orientedPairBase_zero _ (pairConjugate_zero g hg cL) left)
    (orientedPairBase_zero _ (pairConjugate_zero g hg cR) right)
    (he cL left) (he cR right) ε hε
    ((hflat.pairConjugate cL).orientedPairBase left)
    ((hflat.pairConjugate cR).orientedPairBase right) left right ν

attribute [local instance] OAI.Ostmann.quartetTestSymmetriesFintype
theorem conjugated_crossPairMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) (cL cR left right : Bool) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ,
      crossPairMajorant (orientedPairBase (pairConjugate g cL) left)
        (orientedPairBase (pairConjugate g cR) right) left right ρ y) /
          (Fintype.card (ZMod p)ˣ : ℝ)) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  have he (c friendly : Bool) :
      (∑ x : ZMod p, ‖orientedPairBase (pairConjugate g c) friendly x‖ ^ 2) ≤ (p : ℝ) := by
    rw [orientedPairBase_energy]
    simpa only [norm_pairConjugate] using henergy
  exact crossPairMajorant_total_mean_le _ _
    (orientedPairBase_zero _ (pairConjugate_zero g hg cL) left)
    (orientedPairBase_zero _ (pairConjugate_zero g hg cR) right)
    (he cL left) (he cR right) left right

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetLocalBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The six possible moving-leaf pairs and their uniform local estimates -/

namespace Ostmann

open scoped BigOperators

theorem quartetMovingMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (cL cR : Bool) (choice : QuartetMovingCase)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0 ≤ quartetMovingMajorant g cL cR choice ρ y := by
  cases choice with
  | cross left right => exact mul_nonneg (by positivity) (crossPairMajorant_nonneg _ _ _ _ _ _)
  | leftPair =>
    exact mul_nonneg (by norm_num)
      (samePairMajorant_nonneg _ _ (fun _ _ => sq_nonneg _) (fieldPairMoment_nonneg _) _ _)
  | rightPair =>
    exact mul_nonneg (by norm_num)
      (samePairMajorant_nonneg _ _ (fun _ _ => sq_nonneg _) (fieldPairMoment_nonneg _) _ _)

/-- No local-diagram estimate is assumed: this assembles the six previously
proved coefficient bounds on the actual rational-tree value. -/
theorem quartetMoving_coefficient_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (cL cR : Bool) (choice : QuartetMovingCase)
    (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
            (quartetMovingLeaves choice P a b r)) ρ‖ ^ 2) ≤
      quartetMovingMajorant g cL cR choice ρ
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  cases choice with
  | cross left right => exact rationalQuartet_cross_held_bound_conjugation g D Q XL XR P cL cR left right ρ
  | leftPair => exact rationalQuartet_samePair_left_held_bound_conjugation g D Q XL XR P cL cR ρ
  | rightPair => exact rationalQuartet_samePair_right_held_bound_conjugation g D Q XL XR P cL cR ρ

theorem quartetMovingMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (cL cR : Bool) (choice : QuartetMovingCase) (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, quartetMovingMajorant g cL cR choice ρ y) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ quartetLocalMeanError p ε := by
  have hfirst : 0 ≤ 16 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 5 * ε ^ 2 := by positivity
  have hsecond : 0 ≤ 16 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 3 *
      (friendlyQuartetError p ε + twoBadQuartetError p ε) := by
    exact mul_nonneg (by positivity)
      (add_nonneg (friendlyQuartetError_nonneg p ε) (twoBadQuartetError_nonneg p ε))
  cases choice with
  | cross left right =>
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc]
    have h := mul_le_mul_of_nonneg_left
      (conjugated_crossPairMajorant_mean_le g hg henergy ε hε hflat cL cR left right ρ⁻¹)
      (show 0 ≤ 8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 by positivity)
    apply h.trans
    dsimp [quartetLocalMeanError]
    nlinarith
  | leftPair =>
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc]
    have h := mul_le_mul_of_nonneg_left
      (conjugated_samePairMajorant_mean_le g hg ε hε hflat henergy cL cR ρ)
      (show (0 : ℝ) ≤ 8 by norm_num)
    apply h.trans
    dsimp [quartetLocalMeanError]
    nlinarith
  | rightPair =>
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc, sum_units_neg]
    have h := mul_le_mul_of_nonneg_left
      (conjugated_samePairMajorant_mean_le g hg ε hε hflat henergy cR cL ρ)
      (show (0 : ℝ) ≤ 8 by norm_num)
    apply h.trans
    dsimp [quartetLocalMeanError]
    nlinarith

attribute [local instance] OAI.Ostmann.quartetLocalBoundsFintype
theorem quartetMovingMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (cL cR : Bool) (choice : QuartetMovingCase) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ,
      quartetMovingMajorant g cL cR choice ρ y) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤
      8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 := by
  cases choice with
  | cross left right =>
    let F (ρ : MulChar (ZMod p) ℂ) := (∑ y : (ZMod p)ˣ,
      crossPairMajorant (orientedPairBase (pairConjugate g cL) left)
        (orientedPairBase (pairConjugate g cR) right) left right ρ y) /
          (Fintype.card (ZMod p)ˣ : ℝ)
    have hinv := (Equiv.inv (MulChar (ZMod p) ℂ)).bijective.sum_comp F
    change (∑ ρ : MulChar (ZMod p) ℂ, F ρ⁻¹) = ∑ ρ : MulChar (ZMod p) ℂ, F ρ at hinv
    have h := conjugated_crossPairMajorant_total_mean_le g hg henergy cL cR left right
    change (∑ ρ : MulChar (ZMod p) ℂ, F ρ) ≤ _ at h
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc]
    change (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2) *
      (∑ ρ : MulChar (ZMod p) ℂ, F ρ⁻¹) ≤ _
    rw [hinv]
    apply (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq
    ring
  | leftPair =>
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (conjugated_samePairMajorant_total_mean_le g hg henergy cL cR) (by norm_num)
  | rightPair =>
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc, sum_units_neg]
    exact mul_le_mul_of_nonneg_left
      (conjugated_samePairMajorant_total_mean_le g hg henergy cR cL) (by norm_num)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetMovingAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual reciprocal leaf action in the six quartet coordinates -/

namespace Ostmann

open scoped BigOperators

theorem scaleOneLeaf_mul {U : Type*} [CommGroup U] (δ s : ℤ) (z m : U) :
    scaleOneLeaf (δ * s) z m = scaleOneLeaf s (z ^ δ) m := by
  simp only [scaleOneLeaf, zpow_mul]

theorem treeLeafTupleEquiv_scale {U : Type*} [CommGroup U] (n : ℕ)
    (s : TreeLeafTuple ℤ n) (z : U) (m : TreeLeafTuple U n) :
    treeLeafTupleEquiv U n (treeLeafScale n s z m) =
      cycleMultiply (treeLeafTupleEquiv ℤ n s) z (treeLeafTupleEquiv U n m) := by
  funext i
  induction n with
  | zero => rfl
  | succ n ih =>
    cases i with
    | inl i => exact ih s.1 m.1 i
    | inr i => exact ih s.2 m.2 i

theorem quartetMovingLeaves_scale {U : Type*} [CommGroup U]
    (choice : QuartetMovingCase) (P a b r z : U) :
    treeLeafScale 2 (quartetMovingSign choice) z (quartetMovingLeaves choice P a b r) =
      quartetMovingLeaves choice P a b (z * r) := by
  cases choice with
  | cross left right =>
    cases left <;> cases right <;>
      simp [treeLeafScale, scaleOneLeaf, quartetMovingSign, quartetMovingLeaves, crossQuartetLeaves,
        crossLeftLeaves, crossRightLeaves, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  | leftPair =>
    simp [treeLeafScale, scaleOneLeaf, quartetMovingSign, quartetMovingLeaves, samePairLeftLeaves,
      div_eq_mul_inv, mul_assoc, mul_comm]
  | rightPair =>
    simp [treeLeafScale, scaleOneLeaf, quartetMovingSign, quartetMovingLeaves, samePairRightLeaves,
      div_eq_mul_inv, mul_assoc, mul_comm]

theorem treeLeafScale_map_mul {U : Type*} [CommGroup U] (n : ℕ)
    (δ : ℤ) (s : TreeLeafTuple ℤ n) (z : U) (m : TreeLeafTuple U n) :
    treeLeafScale n (treeLeafMap (fun a : ℤ => δ * a) n s) z m =
      treeLeafScale n s (z ^ δ) m := by
  induction n with
  | zero => exact scaleOneLeaf_mul (U := U) δ s z m
  | succ n ih => exact Prod.ext (ih s.1 m.1) (ih s.2 m.2)

theorem quartetMovingLeaves_scaled_sign {U : Type*} [CommGroup U]
    (choice : QuartetMovingCase) (δ : ℤ) (P a b r z : U) :
    treeLeafScale 2 (treeLeafMap (fun s : ℤ => δ * s) 2 (quartetMovingSign choice)) z
      (quartetMovingLeaves choice P a b r) =
      quartetMovingLeaves choice P a b (z ^ δ * r) := by
  rw [treeLeafScale_map_mul, quartetMovingLeaves_scale]

theorem quartetMovingFiberEquiv_symm {U : Type*} [CommGroup U]
    (choice : QuartetMovingCase) (P a b r : U) :
    ((quartetMovingFiberEquiv choice P).symm (a, b, r)).1 =
      quartetMovingLeaves choice P a b r := by
  cases choice with
  | cross left right => exact crossQuartetFiberEquiv_symm left right P a b r
  | leftPair => rfl
  | rightPair => rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProductCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent held and moving coordinates on a product of quartet fibers -/

namespace Ostmann

open scoped BigOperators

theorem quartetProductCoordinates_symm {I U : Type*} [CommGroup U]
    (choice : I → QuartetMovingCase) (P : I → U)
    (h : I → U × U) (r : I → U) (i : I) :
    (((quartetProductCoordinates choice P).symm (h, r)) i).1 =
      quartetMovingLeaves (choice i) (P i) (h i).1 (h i).2 (r i) := by
  exact quartetMovingFiberEquiv_symm (choice i) (P i) (h i).1 (h i).2 (r i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetTreeData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every depth-two tree has the concrete quartet data used by the local bounds -/

namespace Ostmann

theorem RationalTreeData.exists_pair {U : Type*} [CommGroup U] {C : U}
    (T : RationalTreeData U 1 C) :
    ∃ s C₁ C₂ u s₁ s₂ : U, ∃ h : C₁ * C₂ = C,
      h ▸ RationalTreeData.node s C₁ C₂ u
        (.leaf s₁ (u * C₁)) (.leaf s₂ (u * C₂)) = T := by
  cases T with
  | node s C₁ C₂ u left right =>
    cases left with
    | leaf s₁ _ =>
      cases right with
      | leaf s₂ _ => exact ⟨s, C₁, C₂, u, s₁, s₂, rfl, rfl⟩

theorem RationalTreeData.exists_quartet {U : Type*} [CommGroup U] {C : U}
    (T : RationalTreeData U 2 C) :
    ∃ Q : RationalQuartetData U, ∃ h : Q.CL * Q.CR = C, h ▸ Q.tree = T := by
  cases T with
  | node s CL CR u left right =>
    obtain ⟨sL, C₁, C₂, uL, s₁, s₂, hL, eL⟩ := left.exists_pair
    obtain ⟨sR, C₃, C₄, uR, s₃, s₄, hR, eR⟩ := right.exists_pair
    rw [← eL, ← eR]
    exact ⟨⟨s, sL, sR, u, CL, CR, s₁, s₂, s₃, s₄, uL, uR,
      C₁, C₂, C₃, C₄, hL, hR⟩, rfl, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetStateBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local estimates on every depth-two tree arising from the cut -/

namespace Ostmann

open scoped BigOperators

theorem rationalTree_quartet_coefficient_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ 2 C) (XL XR P : (ZMod p)ˣ)
    (cL cR : Bool) (choice : QuartetMovingCase) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D T XL XR ((cL, !cL), (cR, !cR))
            (quartetMovingLeaves choice P a b r)) ρ‖ ^ 2) ≤
      quartetMovingMajorant g cL cR choice ρ (rationalTreeArgument T.frequency C D XL XR P) := by
  obtain ⟨Q, rfl, rfl⟩ := T.exists_quartet
  exact quartetMoving_coefficient_le g D Q XL XR P cL cR choice ρ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProductProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cycle projection of a product of actual quartet states -/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.quartetProjectionCharFintype
attribute [local instance] OAI.Ostmann.quartetProjectionCharDecidableEq
theorem quartetStateProduct_projection_le {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ)
    (S : I → RationalQuartetState p) (P : I → (ZMod p)ˣ)
    (cL cR : I → Bool)
    (hc : ∀ i, (S i).conjugations = ((cL i, !(cL i)), (cR i, !(cR i))))
    (choice : I → QuartetMovingCase) (sign : I → ℤ) :
    ((Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) : ℝ) ^ Fintype.card I)⁻¹ *
      (∑ h : I → (ZMod p)ˣ × (ZMod p)ˣ,
        ((Fintype.card (ZMod p)ˣ : ℝ) ^ Fintype.card I)⁻¹ *
          ∑ r : I → (ZMod p)ˣ,
            ‖cycleAverage sign (quartetStateProduct g D S P choice h) r‖ ^ 2) ≤
      ∑ ρ : I → MulChar (ZMod p) ℂ,
        if (∏ i : I, (ρ i) ^ sign i) = 1 then
          ∏ i : I, quartetMovingMajorant g (cL i) (cR i) (choice i) (ρ i)
            (rationalQuartetStateArgument D (S i) (P i)) else 0 := by
  classical
  unfold quartetStateProduct
  apply held_cycle_product_energy_le
    (fun i (h : (ZMod p)ˣ × (ZMod p)ˣ) r => rationalQuartetStateAmplitude g D (S i)
      (quartetMovingLeaves (choice i) (P i) h.1 h.2 r)) sign
      (fun i ρ => quartetMovingMajorant g (cL i) (cR i) (choice i) ρ
        (rationalQuartetStateArgument D (S i) (P i)))
  intro i ρ
  have h := rationalTree_quartet_coefficient_le g D (S i).tree
    (S i).XL (S i).XR (P i) (cL i) (cR i) (choice i) ρ
  unfold rationalQuartetStateAmplitude rationalQuartetStateArgument
  rw [hc i]
  simpa only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    mul_inv_rev, Finset.mul_sum, mul_assoc] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetFullCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full tree in held and moving quartet coordinates -/

namespace Ostmann

open scoped BigOperators

theorem fullQuartetFiberCoordinates_block {U : Type*} [CommGroup U] (n : ℕ)
    (choice : TreeLeafIndex n → QuartetMovingCase) (P : TreeLeafIndex n → U)
    (h : TreeLeafIndex n → U × U) (r : TreeLeafIndex n → U) (i : TreeLeafIndex n) :
    quartetBlockEquiv U n ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1 i =
      quartetMovingLeaves (choice i) (P i) (h i).1 (h i).2 (r i) := by
  exact (quartetProductFiberEquiv_symm n P _ i).trans
    (quartetProductCoordinates_symm choice P h r i)

theorem mean_fullQuartetFiberCoordinates {U : Type*} [CommGroup U] [Fintype U]
    (n : ℕ) (choice : TreeLeafIndex n → QuartetMovingCase) (P : TreeLeafIndex n → U)
    (f : QuartetProductFiber U n P → ℝ) :
    (Fintype.card (QuartetProductFiber U n P) : ℝ)⁻¹ * (∑ m, f m) =
      ((Fintype.card (U × U) : ℝ) ^ Fintype.card (TreeLeafIndex n))⁻¹ *
        (∑ h : TreeLeafIndex n → U × U,
          ((Fintype.card U : ℝ) ^ Fintype.card (TreeLeafIndex n))⁻¹ *
            ∑ r : TreeLeafIndex n → U, f ((fullQuartetFiberCoordinates n choice P).symm (h, r))) := by
  have hs := (fullQuartetFiberCoordinates n choice P).symm.bijective.sum_comp f
  rw [← hs, Fintype.sum_prod_type,
    Fintype.card_congr (fullQuartetFiberCoordinates n choice P), Fintype.card_prod]
  simp only [Fintype.card_fun, Nat.cast_mul, Nat.cast_pow, mul_inv_rev, Finset.mul_sum]
  congr 1
  ext h
  congr 1
  ext r
  ring

theorem fullQuartetFiberCoordinates_action {U : Type*} [CommGroup U] (n : ℕ)
    (choice : TreeLeafIndex n → QuartetMovingCase) (P : TreeLeafIndex n → U)
    (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
    (hs : ∀ q j, sign (quartetLeafIndex n q j) =
      treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j)
    (h : TreeLeafIndex n → U × U) (r : TreeLeafIndex n → U) (z : U) :
    cycleMultiply sign z (treeLeafTupleEquiv U (n + 2)
      ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1) =
      treeLeafTupleEquiv U (n + 2)
        ((fullQuartetFiberCoordinates n choice P).symm (h, cycleMultiply δ z r)).1 := by
  funext k
  obtain ⟨q, j, hk⟩ : ∃ q j, quartetLeafIndex n q j = k :=
    ⟨_, _, quartetLeafIndex_coordinates n k⟩
  subst k
  change z ^ sign (quartetLeafIndex n q j) *
      treeLeafTupleEquiv U (n + 2) _ (quartetLeafIndex n q j) = _
  rw [← quartetBlockEquiv_read, ← quartetBlockEquiv_read,
    fullQuartetFiberCoordinates_block, fullQuartetFiberCoordinates_block, hs]
  have he := congrArg (fun m => treeLeafTupleEquiv U 2 m j)
    (quartetMovingLeaves_scaled_sign (choice q) (δ q) (P q) (h q).1 (h q).2 (r q) z)
  rw [treeLeafTupleEquiv_scale] at he
  exact he

theorem rationalTreeAmplitude_fullCoordinates {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S)
    (choice : TreeLeafIndex n → QuartetMovingCase)
    (h : TreeLeafIndex n → (ZMod p)ˣ × (ZMod p)ˣ) (r : TreeLeafIndex n → (ZMod p)ˣ) :
    rationalTreeAmplitude g D T XL XR c
      ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1 =
      quartetStateProduct g D (treeLeafTupleEquiv _ n S) P choice h r := by
  rw [rationalTreeAmplitude_product_of_cut g D n T XL XR c P S hS]
  unfold quartetStateProduct
  apply Finset.prod_congr rfl
  intro i _
  rw [fullQuartetFiberCoordinates_block]

theorem cycleAverage_fullCoordinates {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S)
    (choice : TreeLeafIndex n → QuartetMovingCase)
    (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
    (hs : ∀ q j, sign (quartetLeafIndex n q j) =
      treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j)
    (h : TreeLeafIndex n → (ZMod p)ˣ × (ZMod p)ˣ) (r : TreeLeafIndex n → (ZMod p)ˣ) :
    cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
      (treeLeafTupleEquiv _ (n + 2) ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1) =
      cycleAverage δ (quartetStateProduct g D (treeLeafTupleEquiv _ n S) P choice h) r := by
  unfold cycleAverage
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  rw [fullQuartetFiberCoordinates_action n choice P sign δ hs]
  simp only [indexedRationalAmplitude, Equiv.symm_apply_apply]
  exact rationalTreeAmplitude_fullCoordinates g D n T XL XR c P S hS choice h _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProjectedCut
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional projected norm bound on the actual tree cut -/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.projectedCutCharFintype
attribute [local instance] OAI.Ostmann.projectedCutCharDecidableEq
theorem projectedTree_valid_cut_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S)
    (cL cR : TreeLeafIndex n → Bool)
    (hc : ∀ q, quartetBlockEquiv Bool n c q = ((cL q, !(cL q)), (cR q, !(cR q))))
    (choice : TreeLeafIndex n → QuartetMovingCase)
    (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
    (hs : ∀ q j, sign (quartetLeafIndex n q j) =
      treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j) :
    (Fintype.card (QuartetProductFiber (ZMod p)ˣ n P) : ℝ)⁻¹ *
      (∑ m : QuartetProductFiber (ZMod p)ˣ n P,
        ‖cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
          (treeLeafTupleEquiv _ (n + 2) m.1)‖ ^ 2) ≤
      ∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
        if (∏ q : TreeLeafIndex n, (ρ q) ^ δ q) = 1 then
          ∏ q : TreeLeafIndex n, quartetMovingMajorant g (cL q) (cR q) (choice q) (ρ q)
            (rationalQuartetStateArgument D (treeLeafTupleEquiv _ n S q) (P q)) else 0 := by
  rw [mean_fullQuartetFiberCoordinates n choice P]
  simp_rw [cycleAverage_fullCoordinates g D n T XL XR c P S hS choice sign δ hs]
  apply quartetStateProduct_projection_le g D (treeLeafTupleEquiv _ n S) P cL cR
  intro q
  rw [rationalQuartetStates_conjugations_at n T XL XR c _ S hS q]
  exact hc q

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetCutAverages
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projected cut bounds with invalid ancestors included -/

namespace Ostmann

open scoped BigOperators

attribute [local instance] OAI.Ostmann.cutAverageCharDecidableEq
theorem treeLeafTupleEquiv_zip {A B : Type*} (n : ℕ)
    (a : TreeLeafTuple A n) (b : TreeLeafTuple B n) (i : TreeLeafIndex n) :
    treeLeafTupleEquiv (A × B) n (treeLeafZip n a b) i =
      (treeLeafTupleEquiv A n a i, treeLeafTupleEquiv B n b i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases i with
    | inl i => exact ih a.1 b.1 i
    | inr i => exact ih a.2 b.2 i

attribute [local instance] OAI.Ostmann.cutAverageCharFintype
theorem rationalCutCharacterSum_of_valid {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (S : TreeLeafTuple (RationalQuartetState p) n)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = some S)
    (B : TreeLeafIndex n → MulChar (ZMod p) ℂ → ZMod p → ℝ) (δ : TreeLeafIndex n → ℤ) :
    rationalCutCharacterSum D n T XL XR c B δ ((treeLeafTupleEquiv _ n).symm P) =
      ∑ ρ : TreeLeafIndex n → MulChar (ZMod p) ℂ,
        if (∏ q : TreeLeafIndex n, (ρ q) ^ δ q) = 1 then
          ∏ q : TreeLeafIndex n, B q (ρ q)
            (rationalQuartetStateArgument D (treeLeafTupleEquiv _ n S q) (P q)) else 0 := by
  unfold rationalCutCharacterSum
  simp only [hS, quartetCutValue, treeLeafZipProduct_eq_prod, treeLeafTupleEquiv_zip,
    Equiv.apply_symm_apply]
  refine Finset.sum_congr (by ext; simp) fun _ _ => ?_
  congr

theorem rationalTreeAmplitude_zero_of_cut {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) = none)
    (m : QuartetProductFiber (ZMod p)ˣ n P) :
    rationalTreeAmplitude g D T XL XR c m.1 = 0 := by
  have hP : treeLeafMap (treeLeafProduct 2) n (quartetBlockTupleEquiv (ZMod p)ˣ n m.1) =
      (treeLeafTupleEquiv _ n).symm P := by
    apply (treeLeafTupleEquiv _ n).injective
    rw [Equiv.apply_symm_apply, ← quartetProducts_eq_map]
    exact m.property
  rw [rationalTreeAmplitude_cut, hP, hS]
  rfl

theorem projectedTree_cut_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (P : TreeLeafIndex n → (ZMod p)ˣ)
    (cL cR : TreeLeafIndex n → Bool)
    (hc : ∀ q, quartetBlockEquiv Bool n c q = ((cL q, !(cL q)), (cR q, !(cR q))))
    (choice : TreeLeafIndex n → QuartetMovingCase)
    (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
    (hs : ∀ q j, sign (quartetLeafIndex n q j) =
      treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j) :
    (Fintype.card (QuartetProductFiber (ZMod p)ˣ n P) : ℝ)⁻¹ *
      (∑ m : QuartetProductFiber (ZMod p)ˣ n P,
        ‖cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
          (treeLeafTupleEquiv _ (n + 2) m.1)‖ ^ 2) ≤
      rationalCutCharacterSum D n T XL XR c
        (fun q => quartetMovingMajorant g (cL q) (cR q) (choice q)) δ
        ((treeLeafTupleEquiv _ n).symm P) := by
  cases hS : rationalQuartetStates n T XL XR c ((treeLeafTupleEquiv _ n).symm P) with
  | some S =>
    rw [rationalCutCharacterSum_of_valid D n T XL XR c P S hS]
    exact projectedTree_valid_cut_le g D n T XL XR c P S hS cL cR hc choice sign δ hs
  | none =>
    have hz (h : TreeLeafIndex n → (ZMod p)ˣ × (ZMod p)ˣ) (r : TreeLeafIndex n → (ZMod p)ˣ) :
        cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
          (treeLeafTupleEquiv _ (n + 2) ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1) = 0 := by
      unfold cycleAverage
      have hterm (z : (ZMod p)ˣ) :
          indexedRationalAmplitude g D T XL XR c
            (cycleMultiply sign z (treeLeafTupleEquiv _ (n + 2)
              ((fullQuartetFiberCoordinates n choice P).symm (h, r)).1)) = 0 := by
        rw [fullQuartetFiberCoordinates_action n choice P sign δ hs]
        simp only [indexedRationalAmplitude, Equiv.symm_apply_apply]
        exact rationalTreeAmplitude_zero_of_cut g D n T XL XR c P hS _
      simp only [hterm, Finset.sum_const_zero, mul_zero]
    rw [mean_fullQuartetFiberCoordinates n choice P]
    simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero]
    unfold rationalCutCharacterSum
    simp only [hS, quartetCutValue, ite_self, Finset.sum_const_zero, le_refl]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetCycleMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the uniform quartet majorants to a nonempty signed cycle -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetCycleMeanDecidableEq_rfc8d08_1 {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _
theorem quartetLocalMeanError_nonneg (p : ℕ) [Fact p.Prime] (ε : ℝ) :
    0 ≤ quartetLocalMeanError p ε := by
  apply add_nonneg (by positivity)
  exact mul_nonneg (by positivity)
    (add_nonneg (friendlyQuartetError_nonneg p ε) (twoBadQuartetError_nonneg p ε))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetOuterAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the projected bound over all bottom-quartet products -/

namespace Ostmann

open scoped BigOperators

theorem card_treeLeafTuple_quartet {U : Type*} [CommGroup U] [Fintype U]
    (n : ℕ) (P : TreeLeafIndex n → U) :
    Fintype.card (TreeLeafTuple U (n + 2)) =
      Fintype.card (TreeLeafIndex n → U) * Fintype.card (QuartetProductFiber U n P) := by
  rw [card_treeLeafTuple, Fintype.card_fun, card_treeLeafIndex, card_quartetProductFiber,
    ← mul_pow, ← pow_succ', ← pow_mul]
  congr 1
  rw [pow_add]
  norm_num
  omega

theorem mean_treeLeafTuple_by_quartetProducts {U : Type*} [CommGroup U] [Fintype U]
    (n : ℕ) (f : TreeLeafTuple U (n + 2) → ℝ) :
    (∑ m : TreeLeafTuple U (n + 2), f m) /
      (Fintype.card (TreeLeafTuple U (n + 2)) : ℝ) =
      (∑ P : TreeLeafIndex n → U, (Fintype.card (QuartetProductFiber U n P) : ℝ)⁻¹ *
        ∑ m : QuartetProductFiber U n P, f m.1) / (Fintype.card (TreeLeafIndex n → U) : ℝ) := by
  rw [sum_treeLeafTuple_by_quartetProducts]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro P _
  rw [card_treeLeafTuple_quartet n P, Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem projectedTree_mean_le_oai {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2)) (cL cR : TreeLeafIndex n → Bool)
    (hc : ∀ q, quartetBlockEquiv Bool n c q = ((cL q, !(cL q)), (cR q, !(cR q))))
    (choice : TreeLeafIndex n → QuartetMovingCase)
    (sign : TreeLeafIndex (n + 2) → ℤ) (δ : TreeLeafIndex n → ℤ)
    (hs : ∀ q j, sign (quartetLeafIndex n q j) =
      treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j)
    (i : TreeLeafIndex n) (hi : δ i = 1 ∨ δ i = -1) :
    (∑ m : TreeLeafTuple (ZMod p)ˣ (n + 2),
      ‖cycleAverage sign (indexedRationalAmplitude g D T XL XR c)
        (treeLeafTupleEquiv _ (n + 2) m)‖ ^ 2) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ (n + 2)) : ℝ) ≤
      (2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1)) := by
  rw [mean_treeLeafTuple_by_quartetProducts]
  let B := fun q => quartetMovingMajorant g (cL q) (cR q) (choice q)
  calc
    _ ≤ (∑ P : TreeLeafIndex n → (ZMod p)ˣ,
        rationalCutCharacterSum D n T XL XR c B δ ((treeLeafTupleEquiv _ n).symm P)) /
        (Fintype.card (TreeLeafIndex n → (ZMod p)ˣ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun P _ => projectedTree_cut_le g D n T XL XR c P cL cR hc choice sign δ hs
    _ = (∑ P : TreeLeafTuple (ZMod p)ˣ n, rationalCutCharacterSum D n T XL XR c B δ P) /
        (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) := by
      rw [(treeLeafTupleEquiv (ZMod p)ˣ n).symm.sum_comp,
        ← Fintype.card_congr (treeLeafTupleEquiv (ZMod p)ˣ n)]
    _ ≤ _ := rationalCutCharacterSum_mean_le D n T XL XR c B δ i hi
      (quartetLocalMeanError p ε) _ (quartetLocalMeanError_nonneg p ε)
      (fun q ρ y => quartetMovingMajorant_nonneg g (cL q) (cR q) (choice q) ρ y)
      (fun ρ => quartetMovingMajorant_mean_le g hg henergy ε hε hflat (cL i) (cR i) (choice i) ρ)
      (fun q => quartetMovingMajorant_total_mean_le g hg henergy (cL q) (cR q) (choice q))

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.projectedTree_mean_le_oai := @OAI.Ostmann.projectedTree_mean_le_oai
