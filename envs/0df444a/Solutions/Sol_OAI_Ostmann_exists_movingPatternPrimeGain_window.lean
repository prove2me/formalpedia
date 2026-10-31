-- Prove2me | solution 1 for OAI.Ostmann.exists_movingPatternPrimeGain_window
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:16:52.025638+00:00
-- url     : https://prove2.me/submissions/d8e48d1d-95b9-4f3b-b449-6b10b01e4366

import Mathlib
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_projectedTree_mean_le

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSpectatorNode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer pivot gives the spectator's rational reconstruction -/

namespace Ostmann

theorem spectator_frequency_ne_zero {q : ℕ} [Fact q.Prime] (s : ℤ)
    (hs : s ≠ 0) (hsmall : s.natAbs < q) : (s : ZMod q) ≠ 0 := by
  intro hz
  have hd : q ∣ s.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd s q).mp hz)
  exact (not_le_of_gt hsmall) (Nat.le_of_dvd (Int.natAbs_pos.mpr hs) hd)

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
-- module Solutions.OAIQ095_OS.Ostmann_Tree_FiniteActionAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging over the finite cycle action

These are the finite-sum projection identities used in the tree cycle
reduction. The action will be reciprocal multiplication on cycle leaves.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- Averaging does not change correlation against an action-invariant test. -/
theorem finiteActionAverage_correlation {G Ω : Type*} [Group G] [Fintype G]
    [Fintype Ω] [MulAction G Ω] (f h : Ω → ℂ)
    (hh : ∀ (g : G) x, h (g • x) = h x) :
    (∑ x : Ω, finiteActionAverage (G := G) f x * conj (h x)) =
      ∑ x : Ω, f x * conj (h x) := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs (g : G) : (∑ x : Ω, f (g • x) * conj (h x)) =
      ∑ x : Ω, f x * conj (h x) := by
    calc
      _ = ∑ x : Ω, f (g • x) * conj (h (g • x)) := by simp only [hh]
      _ = _ := (actionPermutation g).bijective.sum_comp (fun x => f x * conj (h x))
  simp only [finiteActionAverage, Finset.sum_mul, mul_assoc]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CycleAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal multiplication on cycle leaves

An integer sign on each leaf specifies multiplication by `z` or its inverse.
A block whose signs sum to zero has its product preserved by this action.
Thus a balanced cycle preserves both component totals and quartet totals.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem cycleMultiply_product {I G : Type*} [CommGroup G]
    (s : Finset I) (sign : I → ℤ) (z : G) (m : I → G) :
    (∏ i ∈ s, cycleMultiply sign z m i) = z ^ (∑ i ∈ s, sign i) * ∏ i ∈ s, m i := by
  classical
  have hp : (∏ i ∈ s, z ^ sign i) = z ^ (∑ i ∈ s, sign i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih, zpow_add]
  simp only [cycleMultiply, Finset.prod_mul_distrib, hp]

theorem cycleMultiply_preserves_product {I G : Type*} [CommGroup G]
    (s : Finset I) (sign : I → ℤ) (hs : ∑ i ∈ s, sign i = 0) (z : G) (m : I → G) :
    (∏ i ∈ s, cycleMultiply sign z m i) = ∏ i ∈ s, m i := by
  rw [cycleMultiply_product, hs, zpow_zero, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarePullback
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

theorem additiveFourier_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => c * f x) a = c * additiveFourier f a := by
  simp only [additiveFourier_apply, mul_assoc]
  rw [← Finset.mul_sum]
  ring

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BottomPairMellin
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TreeDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Iterating the elementary tree density estimate

A split plan allows the remaining unit parameters to depend on every
previous split coordinate. The bound is uniform over those choices.
The separate rational-coordinate lemmas identify the manuscript's tree
with this inverse-square split law on valid ancestor data.
-/

namespace Ostmann

open scoped BigOperators

theorem treeDensityMajorant_zero {p : ℕ} [Fact p.Prime] (w : ZMod p → ℝ) (n : ℕ) :
    treeDensityMajorant w n 0 = 0 := by
  cases n <;> simp [treeDensityMajorant]

theorem treeDensityMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (n : ℕ) (d : ZMod p) :
    0 ≤ treeDensityMajorant w n d := by
  induction n generalizing d with
  | zero => simp only [treeDensityMajorant]; split_ifs; exact le_rfl; exact hw d
  | succ n ih =>
    simp only [treeDensityMajorant]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by positivity) (differenceMoment_nonneg _ _ ih ih d)

theorem treeDensityMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (E : ℝ)
    (hE : (∑ d : (ZMod p)ˣ, w d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ E) (n : ℕ) :
    (∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ binaryMomentBound E n := by
  have hU : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  induction n with
  | zero =>
    simpa only [treeDensityMajorant, Units.ne_zero, ite_false, if_false, binaryMomentBound] using hE
  | succ n ih =>
    have hzero := treeDensityMajorant_zero w n
    have hsum := sum_units_eq_sum_of_zero (treeDensityMajorant w n) hzero
    have hnn : 0 ≤ (∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
        (Fintype.card (ZMod p)ˣ : ℝ) := by
      apply div_nonneg _ hU.le
      exact Finset.sum_nonneg fun d _ => treeDensityMajorant_nonneg w hw n d
    calc
      _ = (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
          (∑ d : (ZMod p)ˣ,
            differenceMoment (treeDensityMajorant w n) (treeDensityMajorant w n) d) /
            (Fintype.card (ZMod p)ˣ : ℝ) := by
        simp only [treeDensityMajorant, Units.ne_zero, ite_false, if_false, ← Finset.mul_sum]
      _ ≤ (2 / (Fintype.card (ZMod p)ˣ : ℝ)) *
          ((∑ x : ZMod p, treeDensityMajorant w n x) ^ 2) /
            (Fintype.card (ZMod p)ˣ : ℝ) := by
        apply div_le_div_of_nonneg_right _ hU.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [pow_two] using sum_units_differenceMoment_le
          (treeDensityMajorant w n) (treeDensityMajorant w n)
          (treeDensityMajorant_nonneg w hw n) (treeDensityMajorant_nonneg w hw n)
      _ = 2 * ((∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
          (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by rw [← hsum]; ring
      _ ≤ 2 * binaryMomentBound E n ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn ih 2) (by norm_num)
      _ = _ := rfl

/-- The recursive density bound in closed form. -/
theorem binaryMomentBound_eq (E : ℝ) (n : ℕ) :
    binaryMomentBound E n = (2 * E) ^ (2 ^ n) / 2 := by
  induction n with
  | zero => simp [binaryMomentBound]
  | succ n ih =>
    rw [binaryMomentBound, ih, pow_succ (2 : ℕ), pow_mul]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem rationalTreeMoment_nonneg {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (XL XR P : (ZMod p)ˣ) : 0 ≤ rationalTreeMoment w D T XL XR P := by
  induction T generalizing XL XR P with
  | leaf s C => exact hw _
  | node s CL CR u left right ihL ihR =>
    simp only [rationalTreeMoment]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro m _
    dsimp
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (ihL _ _ _) (ihR _ _ _)

/-- The actual recursive rational-node moment is bounded by the uniform density majorant. -/
theorem rationalTreeMoment_le_majorant {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (D : (ZMod p)ˣ)
    {n : ℕ} {C : (ZMod p)ˣ} (T : RationalTreeData (ZMod p)ˣ n C)
    (XL XR P : (ZMod p)ˣ) :
    rationalTreeMoment w D T XL XR P ≤
      treeDensityMajorant w n (rationalTreeArgument T.frequency C D XL XR P) := by
  induction T generalizing XL XR P with
  | leaf s C =>
    simp only [rationalTreeMoment, RationalTreeData.frequency, treeDensityMajorant,
      Units.ne_zero, ite_false, if_false, le_refl]
  | @node n s CL CR u left right ihL ihR =>
    have harg := rationalTreeArgument_node s CL CR D XL XR P
    change _ ≤ treeDensityMajorant w (n + 1) (rationalTreeArgument s (CL * CR) D XL XR P)
    rw [harg]
    simp only [treeDensityMajorant, Units.ne_zero, ite_false, if_false]
    calc
      _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ m : (ZMod p)ˣ, rationalNodeValue s left.frequency right.frequency D u XL XR CL CR P
            (treeDensityMajorant w n) (treeDensityMajorant w n) m := by
        unfold rationalTreeMoment
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro m _
        dsimp [rationalNodeValue]
        split_ifs with hv
        · exact le_rfl
        · have hL := ihL (Units.mk0 _ hv) XL m
          have hR := ihR (Units.mk0 _ hv) XR (P / m)
          rw [rationalTreeArgument_child] at hL hR
          exact mul_le_mul hL hR (rationalTreeMoment_nonneg w hw D right _ _ _)
            (treeDensityMajorant_nonneg w hw n _)
      _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          (2 * ∑ x : ZMod p, treeDensityMajorant w n x *
            treeDensityMajorant w n (x - rationalNodeArgument s D XL XR CL CR P)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact rationalNodeValue_sum_le s left.frequency right.frequency D u XL XR CL CR P
          _ _ (treeDensityMajorant_zero w n) (treeDensityMajorant_zero w n)
          (treeDensityMajorant_nonneg w hw n) (treeDensityMajorant_nonneg w hw n)
      _ = _ := by unfold differenceMoment; ring

theorem rationalTreeMoment_mean_le {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (hw : ∀ x, 0 ≤ w x) (E : ℝ)
    (hE : (∑ d : (ZMod p)ˣ, w d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ E)
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ P : (ZMod p)ˣ, rationalTreeMoment w D T XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ binaryMomentBound E n := by
  calc
    _ ≤ (∑ P : (ZMod p)ˣ,
        treeDensityMajorant w n (rationalTreeArgument T.frequency C D XL XR P)) /
          (Fintype.card (ZMod p)ˣ : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun P _ => rationalTreeMoment_le_majorant w hw D T XL XR P
    _ = (∑ d : (ZMod p)ˣ, treeDensityMajorant w n d) /
          (Fintype.card (ZMod p)ˣ : ℝ) := by
      congr 1
      exact (rationalTreeArgumentEquiv T.frequency C D XL XR).sum_comp
        (fun d => treeDensityMajorant w n d)
    _ ≤ _ := treeDensityMajorant_mean_le w hw E hE n

/-- The actual rational tree, averaged in its root product, satisfies `src37`. -/
theorem rationalTreeMoment_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ P : (ZMod p)ˣ, rationalTreeMoment (fun x => ‖g x‖ ^ 2) D T XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have hpr : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  have hsum := sum_units_eq_sum_of_zero (fun x => ‖g x‖ ^ 2) (by simp [hg])
  have hE : (∑ d : (ZMod p)ˣ, ‖g d‖ ^ 2) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ 3 / 2 := by
    rw [hU, hsum]
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
    linarith
  have h := rationalTreeMoment_mean_le (fun x => ‖g x‖ ^ 2) (fun _ => sq_nonneg _)
    (3 / 2) hE D T XL XR
  rw [binaryMomentBound_eq] at h
  norm_num only [show (2 : ℝ) * (3 / 2) = 3 by norm_num] at h
  exact h.trans (by have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (2 ^ n); linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTreeLeaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational tree under independent uniform leaf sampling -/

namespace Ostmann

open scoped BigOperators

theorem rationalTreeLeafValue_fiber_sum {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR P : (ZMod p)ˣ) :
    (∑ x : TreeLeafFiber (ZMod p)ˣ n P, rationalTreeLeafValue w D T XL XR x.1) =
      (Fintype.card (ZMod p)ˣ : ℝ) ^ (2 ^ n - 1) * rationalTreeMoment w D T XL XR P := by
  induction T generalizing XL XR P with
  | leaf s C =>
    have he : ∀ x : TreeLeafFiber (ZMod p)ˣ 0 P, (x.1 : (ZMod p)ˣ) = P :=
      fun x => x.property
    simp only [rationalTreeLeafValue, he, Finset.sum_const, Finset.card_univ,
      card_treeLeafFiber, pow_zero, Nat.sub_self, pow_zero, one_smul, one_mul,
      rationalTreeMoment]
  | @node n s CL CR u left right ihL ihR =>
    rw [sum_treeLeafFiber_succ]
    have hterm (m : (ZMod p)ˣ) :
        (∑ a : TreeLeafFiber (ZMod p)ˣ n m,
          ∑ b : TreeLeafFiber (ZMod p)ˣ n (P / m),
            rationalTreeLeafValue w D (.node s CL CR u left right) XL XR (a.1, b.1)) =
        ((Fintype.card (ZMod p)ˣ : ℝ) ^ (2 ^ n - 1)) ^ 2 *
          (let HL : (ZMod p)ˣ := XL * CL * m
           let HR : (ZMod p)ˣ := XR * CR * (P / m)
           let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
           if hv : v = 0 then 0 else
             rationalTreeMoment w D left (Units.mk0 v hv) XL m *
               rationalTreeMoment w D right (Units.mk0 v hv) XR (P / m)) := by
      have hfib {Q : (ZMod p)ˣ} (x : TreeLeafFiber (ZMod p)ˣ n Q) :
          treeLeafProduct n x.1 = Q := x.property
      simp only [rationalTreeLeafValue, hfib]
      dsimp
      split_ifs with hv
      · simp
      · let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u
          ((XL : ZMod p) * CL * m) ((XR : ZMod p) * CR * (P / m : (ZMod p)ˣ))
        let V : (ZMod p)ˣ := Units.mk0 v hv
        change (∑ a : TreeLeafFiber (ZMod p)ˣ n m,
          ∑ b : TreeLeafFiber (ZMod p)ˣ n (P / m),
            rationalTreeLeafValue w D left V XL a.1 *
            rationalTreeLeafValue w D right V XR b.1) = _
        rw [← Fintype.sum_mul_sum
          (fun a : TreeLeafFiber (ZMod p)ˣ n m => rationalTreeLeafValue w D left V XL a.1)
          (fun b : TreeLeafFiber (ZMod p)ˣ n (P / m) => rationalTreeLeafValue w D right V XR b.1)]
        rw [ihL, ihR]
        ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    simp only [rationalTreeMoment]
    have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    have hexp : 2 ^ (n + 1) - 1 = (2 ^ n - 1) * 2 + 1 := by
      rw [pow_succ]
      omega
    rw [hexp]
    conv_rhs => arg 1; rw [pow_succ, pow_mul]
    field_simp

theorem rationalTreeLeafValue_mean_eq {p : ℕ} [Fact p.Prime]
    (w : ZMod p → ℝ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n, rationalTreeLeafValue w D T XL XR x) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) =
    (∑ P : (ZMod p)ˣ, rationalTreeMoment w D T XL XR P) /
      (Fintype.card (ZMod p)ˣ : ℝ) := by
  rw [sum_treeLeafTuple_by_product]
  simp_rw [rationalTreeLeafValue_fiber_sum]
  rw [← Finset.mul_sum, card_treeLeafTuple, Nat.cast_pow]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  conv_lhs => rhs; rw [← Nat.sub_add_cancel hn, pow_succ]
  field_simp

/-- The first part of the tree comparison: independent uniform leaves give the `3^r` bound. -/
theorem rationalTreeLeafValue_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n,
      rationalTreeLeafValue (fun y => ‖g y‖ ^ 2) D T XL XR x) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  rw [rationalTreeLeafValue_mean_eq]
  exact rationalTreeMoment_l2_bound hp g hg henergy D T XL XR

theorem norm_rationalTreeAmplitude_sq {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) (m : TreeLeafTuple (ZMod p)ˣ n) :
    ‖rationalTreeAmplitude g D T XL XR c m‖ ^ 2 =
      rationalTreeLeafValue (fun y => ‖g y‖ ^ 2) D T XL XR m := by
  induction T generalizing XL XR with
  | leaf s C =>
    cases c <;> simp [rationalTreeAmplitude, rationalTreeLeafValue]
  | node s CL CR u left right ihL ihR =>
    simp only [rationalTreeAmplitude, rationalTreeLeafValue]
    split_ifs
    · simp
    · rw [norm_mul, mul_pow, ihL, ihR]

/-- Equation `src37`, with the actual reconstructed-node diagram and uniform independent leaves. -/
theorem rationalTreeAmplitude_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) :
    (∑ m : TreeLeafTuple (ZMod p)ˣ n, ‖rationalTreeAmplitude g D T XL XR c m‖ ^ 2) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  simp_rw [norm_rationalTreeAmplitude_sq]
  exact rationalTreeLeafValue_l2_bound hp g hg henergy D T XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeLeafIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Labeled leaves and bottom quartets of a full binary tree -/

namespace Ostmann

open scoped BigOperators

theorem indexedRationalAmplitude_l2_bound {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) :
    (∑ m : TreeLeafIndex n → (ZMod p)ˣ, ‖indexedRationalAmplitude g D T XL XR c m‖ ^ 2) /
      (Fintype.card (TreeLeafIndex n → (ZMod p)ˣ) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have hsum := (treeLeafTupleEquiv (ZMod p)ˣ n).symm.sum_comp
    (fun m => ‖rationalTreeAmplitude g D T XL XR c m‖ ^ 2)
  have hcard := Fintype.card_congr (treeLeafTupleEquiv (ZMod p)ˣ n)
  change (∑ m : TreeLeafIndex n → (ZMod p)ˣ,
    ‖rationalTreeAmplitude g D T XL XR c ((treeLeafTupleEquiv (ZMod p)ˣ n).symm m)‖ ^ 2) /
    (Fintype.card (TreeLeafIndex n → (ZMod p)ˣ) : ℝ) ≤ _
  rw [hsum, ← hcard]
  exact rationalTreeAmplitude_l2_bound hp g hg henergy D T XL XR c

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
-- module Solutions.OAIQ095_OS.Ostmann_Tree_IncidenceCycle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A cycle in the component--quartet incidence diagram

There is one edge per leaf. Parallel edges already give the two-edge
cycle used in the manuscript; otherwise the incidence graph is simple,
and at least as many edges as vertices force a cycle.
-/

namespace Ostmann

/-- A finite forest on a nonempty vertex set has fewer edges than vertices. -/
theorem forest_card_edges_lt {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (hG : G.IsAcyclic) :
    G.edgeFinset.card < Fintype.card V := by
  classical
  obtain ⟨T, hGT, _, hT⟩ :=
    (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
      (show G ≤ ⊤ from le_top) hG
  have hcard := hT.card_edgeFinset
  have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
  omega

theorem exists_cycle_of_card_edges_ge {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (hcard : Fintype.card V ≤ G.edgeFinset.card) :
    ∃ v : V, ∃ c : G.Walk v v, c.IsCycle := by
  classical
  have h : ¬G.IsAcyclic := fun hG => (not_lt_of_ge hcard) (forest_card_edges_lt G hG)
  unfold SimpleGraph.IsAcyclic at h
  push Not at h
  exact h

/-- The incidence diagram has either parallel leaves or a genuine simple cycle. -/
theorem incidence_parallel_or_cycle {L C Q : Type*} [Fintype L] [Fintype C] [Fintype Q]
    [Nonempty L] (component : L → C) (quartet : L → Q)
    (hcard : Fintype.card C + Fintype.card Q ≤ Fintype.card L) :
    (∃ i j : L, i ≠ j ∧ component i = component j ∧ quartet i = quartet j) ∨
      ∃ v : C ⊕ Q, ∃ c : (incidenceGraph component quartet).Walk v v, c.IsCycle := by
  classical
  by_cases hinj : Function.Injective (fun i => (component i, quartet i))
  · right
    let : Nonempty (C ⊕ Q) := ⟨.inl (component (Classical.choice ‹Nonempty L›))⟩
    let G := incidenceGraph component quartet
    let edge : L → G.edgeFinset := fun i =>
      ⟨s(Sum.inl (component i), Sum.inr (quartet i)), by
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact ⟨i, rfl, rfl⟩⟩
    have hedge : Function.Injective edge := by
      intro i j hij
      have he := congrArg (fun e : G.edgeFinset => e.1) hij
      rcases Sym2.eq_iff.mp he with h | h
      · apply hinj
        exact Prod.ext (Sum.inl.inj h.1) (Sum.inr.inj h.2)
      · cases h.1
    have hle := Fintype.card_le_of_injective edge hedge
    have hV : Fintype.card (C ⊕ Q) ≤ G.edgeFinset.card := by
      simpa only [Fintype.card_sum, Fintype.card_coe] using hcard.trans hle
    exact exists_cycle_of_card_edges_ge G hV
  · left
    simp only [Function.Injective, Prod.mk.injEq, not_forall] at hinj
    obtain ⟨i, j, ⟨hc, hq⟩, hne⟩ := hinj
    exact ⟨i, j, hne, hc, hq⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_IncidenceCirculation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A balanced leaf action from an incidence-graph cycle -/

namespace Ostmann

open scoped BigOperators

theorem list_sum_finset_sum {X I R : Type*} [AddCommMonoid R]
    (xs : List X) (s : Finset I) (f : I → X → R) :
    (∑ i ∈ s, (xs.map (f i)).sum) = (xs.map fun x => ∑ i ∈ s, f i x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem walk_dart_difference {V R : Type*} [AddCommGroup R] {G : SimpleGraph V}
    {u v : V} (w : G.Walk u v) (f : V → R) :
    (w.darts.map fun d => f d.fst - f d.snd).sum = f u - f v := by
  induction w with
  | nil => simp
  | cons h w ih =>
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]
    abel

theorem walk_dart_reverse_difference {V R : Type*} [AddCommGroup R] {G : SimpleGraph V}
    {u v : V} (w : G.Walk u v) (f : V → R) :
    (w.darts.map fun d => f d.snd - f d.fst).sum = f v - f u := by
  induction w with
  | nil => simp
  | cons h w ih =>
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]
    abel

theorem incidenceDartLabel_spec {L C Q : Type*} (component : L → C) (quartet : L → Q)
    (d : (incidenceGraph component quartet).Dart) :
    (d.fst = Sum.inl (component (incidenceDartLabel component quartet d)) ∧
      d.snd = Sum.inr (quartet (incidenceDartLabel component quartet d))) ∨
    (d.fst = Sum.inr (quartet (incidenceDartLabel component quartet d)) ∧
      d.snd = Sum.inl (component (incidenceDartLabel component quartet d))) :=
  Classical.choose_spec (incidenceDart_exists component quartet d)

theorem incidenceWalkSign_block_sum {L C Q B : Type*} [Fintype L] [DecidableEq L]
    [DecidableEq B] (component : L → C) (quartet : L → Q) {u v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk u v) (block : L → B) (b : B) :
    (∑ i ∈ Finset.univ.filter (fun i => block i = b), incidenceWalkSign component quartet w i) =
      (w.darts.map fun d => if block (incidenceDartLabel component quartet d) = b
        then incidenceDartSign d else 0).sum := by
  unfold incidenceWalkSign
  rw [list_sum_finset_sum]
  congr 1
  apply List.map_congr_left
  intro d _
  simp

theorem incidenceDart_component_difference {L C Q : Type*} [DecidableEq C] [DecidableEq Q]
    (component : L → C) (quartet : L → Q) (d : (incidenceGraph component quartet).Dart) (c : C) :
    (if component (incidenceDartLabel component quartet d) = c then incidenceDartSign d else 0) =
      (if d.fst = Sum.inl c then (1 : ℤ) else 0) - (if d.snd = Sum.inl c then 1 else 0) := by
  rcases incidenceDartLabel_spec component quartet d with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · simp [incidenceDartSign, hfst, hsnd]
  · simp only [incidenceDartSign, hfst, hsnd, Sum.inl.injEq,
      Sum.inr_ne_inl, ite_false, if_false, zero_sub]
    split_ifs <;> rfl

theorem incidenceDart_quartet_difference {L C Q : Type*} [DecidableEq C] [DecidableEq Q]
    (component : L → C) (quartet : L → Q) (d : (incidenceGraph component quartet).Dart) (q : Q) :
    (if quartet (incidenceDartLabel component quartet d) = q then incidenceDartSign d else 0) =
      (if d.snd = Sum.inr q then (1 : ℤ) else 0) - (if d.fst = Sum.inr q then 1 else 0) := by
  rcases incidenceDartLabel_spec component quartet d with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · simp [incidenceDartSign, hfst, hsnd]
  · simp only [incidenceDartSign, hfst, hsnd, Sum.inr.injEq,
      Sum.inl_ne_inr, ite_false, if_false, zero_sub]
    split_ifs <;> rfl

theorem incidenceWalkSign_component_balanced {L C Q : Type*} [Fintype L] [DecidableEq L]
    [DecidableEq C] [DecidableEq Q] (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (c : C) :
    (∑ i ∈ Finset.univ.filter (fun i => component i = c), incidenceWalkSign component quartet w i) = 0 := by
  rw [incidenceWalkSign_block_sum]
  simp_rw [incidenceDart_component_difference]
  simpa only [sub_self] using walk_dart_difference w
    (fun x : C ⊕ Q => if x = Sum.inl c then (1 : ℤ) else 0)

theorem incidenceWalkSign_quartet_balanced {L C Q : Type*} [Fintype L] [DecidableEq L]
    [DecidableEq C] [DecidableEq Q] (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (q : Q) :
    (∑ i ∈ Finset.univ.filter (fun i => quartet i = q), incidenceWalkSign component quartet w i) = 0 := by
  rw [incidenceWalkSign_block_sum]
  simp_rw [incidenceDart_quartet_difference]
  simpa only [sub_self] using walk_dart_reverse_difference w
    (fun x : C ⊕ Q => if x = Sum.inr q then (1 : ℤ) else 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ParallelCycle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-edge cycle

Two leaves in the same component and the same quartet give a balanced
sign vector supported on precisely those two leaves. No additional
assumption is needed for this degenerate cycle.
-/

namespace Ostmann

open scoped BigOperators

theorem parallelCycleSign_left {I : Type*} [DecidableEq I] (i j : I) (hij : i ≠ j) :
    parallelCycleSign i j i = 1 := by simp [parallelCycleSign, hij]

theorem parallelCycleSign_right {I : Type*} [DecidableEq I] (i j : I) (hij : i ≠ j) :
    parallelCycleSign i j j = -1 := by simp [parallelCycleSign, Ne.symm hij]

theorem parallelCycleSign_other {I : Type*} [DecidableEq I] (i j k : I)
    (hki : k ≠ i) (hkj : k ≠ j) : parallelCycleSign i j k = 0 := by
  simp [parallelCycleSign, hki, hkj]

theorem sum_parallelCycleSign {I : Type*} [DecidableEq I] (s : Finset I) (i j : I) :
    (∑ k ∈ s, parallelCycleSign i j k) =
      (if i ∈ s then 1 else 0) - (if j ∈ s then 1 else 0) := by
  simp [parallelCycleSign, Finset.sum_sub_distrib]

/-- The same block membership cancels the two signs. -/
theorem parallelCycleSign_balanced {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (block : I → J) (i j : I) (hij : block i = block j) (b : J) :
    (∑ k ∈ Finset.univ.filter (fun k => block k = b), parallelCycleSign i j k) = 0 := by
  rw [sum_parallelCycleSign]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hij, sub_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_IncidenceCycleSigns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonzero balanced sign vector supplied by an incidence cycle -/

namespace Ostmann

open scoped BigOperators

theorem list_label_sum_eq_zero {X L R : Type*} [DecidableEq L] [AddCommMonoid R]
    (xs : List X) (label : X → L) (f : X → R) (i : L) (hi : i ∉ xs.map label) :
    (xs.map fun x => if label x = i then f x else 0).sum = 0 := by
  apply List.sum_eq_zero
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  have hne : label x ≠ i := fun h => hi (List.mem_map.mpr ⟨x, hx, h⟩)
  simp only [hne, ite_false, if_false]

theorem list_label_sum_of_mem {X L R : Type*} [DecidableEq L] [AddCommMonoid R]
    (xs : List X) (label : X → L) (f : X → R) (h : (xs.map label).Nodup)
    (x : X) (hx : x ∈ xs) :
    (xs.map fun y => if label y = label x then f y else 0).sum = f x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with hxy | hx
    · subst x
      simp only [List.map_cons, List.sum_cons, ite_true, if_true]
      rw [list_label_sum_eq_zero ys label f (label y) h.1, add_zero]
    · have hne : label y ≠ label x := fun heq => h.1 (List.mem_map.mpr ⟨x, hx, heq.symm⟩)
      simp only [List.map_cons, List.sum_cons, hne, ite_false, if_false, zero_add]
      exact ih h.2 hx

theorem incidenceDart_edge_of_label {L C Q : Type*}
    (component : L → C) (quartet : L → Q) (d : (incidenceGraph component quartet).Dart) :
    d.edge = s(Sum.inl (component (incidenceDartLabel component quartet d)),
      Sum.inr (quartet (incidenceDartLabel component quartet d))) := by
  rcases incidenceDartLabel_spec component quartet d with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · simp only [SimpleGraph.Dart.edge, hfst, hsnd]
  · simp only [SimpleGraph.Dart.edge, hfst, hsnd, Sym2.eq_swap]

theorem incidenceWalk_labels_nodup {L C Q : Type*}
    (component : L → C) (quartet : L → Q) {u v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk u v) (hw : w.IsTrail) :
    (w.darts.map (incidenceDartLabel component quartet)).Nodup := by
  let edge : L → Sym2 (C ⊕ Q) := fun i => s(Sum.inl (component i), Sum.inr (quartet i))
  have hmap : (w.darts.map (incidenceDartLabel component quartet)).map edge = w.edges := by
    rw [List.map_map, SimpleGraph.Walk.edges]
    apply List.map_congr_left
    intro d _
    exact (incidenceDart_edge_of_label component quartet d).symm
  exact List.Nodup.of_map edge (hmap.symm ▸ hw.edges_nodup)

theorem incidenceDartSign_eq_one_or_neg_one {L C Q : Type*}
    {component : L → C} {quartet : L → Q} (d : (incidenceGraph component quartet).Dart) :
    incidenceDartSign d = 1 ∨ incidenceDartSign d = -1 := by
  unfold incidenceDartSign
  cases d.fst <;> simp

theorem incidenceWalkSign_values {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {u v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk u v) (hw : w.IsTrail) (i : L) :
    incidenceWalkSign component quartet w i = 0 ∨
      incidenceWalkSign component quartet w i = 1 ∨ incidenceWalkSign component quartet w i = -1 := by
  by_cases hi : i ∈ w.darts.map (incidenceDartLabel component quartet)
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hi
    right
    rw [incidenceWalkSign, list_label_sum_of_mem _ _ _ (incidenceWalk_labels_nodup component quartet w hw) d hd]
    exact incidenceDartSign_eq_one_or_neg_one d
  · left
    exact list_label_sum_eq_zero _ _ _ i hi

theorem incidenceCycleSign_nonzero {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (hw : w.IsCycle) :
    ∃ i : L, incidenceWalkSign component quartet w i = 1 ∨ incidenceWalkSign component quartet w i = -1 := by
  have hne : w.darts ≠ [] := fun h => hw.not_nil (SimpleGraph.Walk.darts_eq_nil.mp h)
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil w.darts hne
  refine ⟨incidenceDartLabel component quartet d, ?_⟩
  rw [incidenceWalkSign, list_label_sum_of_mem _ _ _
    (incidenceWalk_labels_nodup component quartet w hw.isTrail) d hd]
  exact incidenceDartSign_eq_one_or_neg_one d

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CycleQuartets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A simple cycle moves at most two leaves in each quartet -/

namespace Ostmann

open scoped BigOperators

theorem incidenceDart_positive_target {L C Q : Type*}
    (component : L → C) (quartet : L → Q) (d : (incidenceGraph component quartet).Dart)
    (hd : incidenceDartSign d = 1) :
    d.snd = Sum.inr (quartet (incidenceDartLabel component quartet d)) := by
  rcases incidenceDartLabel_spec component quartet d with ⟨_, hsnd⟩ | ⟨hfst, _⟩
  · exact hsnd
  · simp [incidenceDartSign, hfst] at hd

theorem incidenceDart_negative_source {L C Q : Type*}
    (component : L → C) (quartet : L → Q) (d : (incidenceGraph component quartet).Dart)
    (hd : incidenceDartSign d = -1) :
    d.fst = Sum.inr (quartet (incidenceDartLabel component quartet d)) := by
  rcases incidenceDartLabel_spec component quartet d with ⟨hfst, _⟩ | ⟨hfst, _⟩
  · simp [incidenceDartSign, hfst] at hd
  · exact hfst

theorem exists_dart_of_incidenceWalkSign_ne_zero {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {u v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk u v) (i : L)
    (hi : incidenceWalkSign component quartet w i ≠ 0) :
    ∃ d ∈ w.darts, incidenceDartLabel component quartet d = i := by
  by_contra h
  apply hi
  apply list_label_sum_eq_zero
  simpa only [List.mem_map, not_exists, not_and] using h

theorem incidenceCycle_positive_unique {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (hw : w.IsCycle)
    (i j : L) (hi : incidenceWalkSign component quartet w i = 1)
    (hj : incidenceWalkSign component quartet w j = 1) (hq : quartet i = quartet j) : i = j := by
  obtain ⟨d, hd, hdi⟩ := exists_dart_of_incidenceWalkSign_ne_zero component quartet w i
    (by rw [hi]; norm_num)
  obtain ⟨e, he, hej⟩ := exists_dart_of_incidenceWalkSign_ne_zero component quartet w j
    (by rw [hj]; norm_num)
  have hds : incidenceDartSign d = 1 := by
    have h := list_label_sum_of_mem w.darts (incidenceDartLabel component quartet) incidenceDartSign
      (incidenceWalk_labels_nodup component quartet w hw.isTrail) d hd
    change incidenceWalkSign component quartet w (incidenceDartLabel component quartet d) = _ at h
    rw [hdi, hi] at h
    exact h.symm
  have hes : incidenceDartSign e = 1 := by
    have h := list_label_sum_of_mem w.darts (incidenceDartLabel component quartet) incidenceDartSign
      (incidenceWalk_labels_nodup component quartet w hw.isTrail) e he
    change incidenceWalkSign component quartet w (incidenceDartLabel component quartet e) = _ at h
    rw [hej, hj] at h
    exact h.symm
  have hnd : (w.darts.map (fun d => d.snd)).Nodup := by
    rw [SimpleGraph.Walk.map_snd_darts]
    exact hw.support_nodup
  have hde : d = e := List.inj_on_of_nodup_map hnd hd he (by
    rw [incidenceDart_positive_target component quartet d hds,
      incidenceDart_positive_target component quartet e hes, hdi, hej, hq])
  exact hdi.symm.trans ((congrArg (incidenceDartLabel component quartet) hde).trans hej)

theorem incidenceCycle_negative_unique {L C Q : Type*} [DecidableEq L]
    (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (hw : w.IsCycle)
    (i j : L) (hi : incidenceWalkSign component quartet w i = -1)
    (hj : incidenceWalkSign component quartet w j = -1) (hq : quartet i = quartet j) : i = j := by
  obtain ⟨d, hd, hdi⟩ := exists_dart_of_incidenceWalkSign_ne_zero component quartet w i
    (by rw [hi]; norm_num)
  obtain ⟨e, he, hej⟩ := exists_dart_of_incidenceWalkSign_ne_zero component quartet w j
    (by rw [hj]; norm_num)
  have hds : incidenceDartSign d = -1 := by
    have h := list_label_sum_of_mem w.darts (incidenceDartLabel component quartet) incidenceDartSign
      (incidenceWalk_labels_nodup component quartet w hw.isTrail) d hd
    change incidenceWalkSign component quartet w (incidenceDartLabel component quartet d) = _ at h
    rw [hdi, hi] at h
    exact h.symm
  have hes : incidenceDartSign e = -1 := by
    have h := list_label_sum_of_mem w.darts (incidenceDartLabel component quartet) incidenceDartSign
      (incidenceWalk_labels_nodup component quartet w hw.isTrail) e he
    change incidenceWalkSign component quartet w (incidenceDartLabel component quartet e) = _ at h
    rw [hej, hj] at h
    exact h.symm
  have hnd : (w.darts.map (fun d => d.fst)).Nodup := by
    rw [SimpleGraph.Walk.map_fst_darts]
    exact hw.nodup_dropLast_support
  have hde : d = e := List.inj_on_of_nodup_map hnd hd he (by
    rw [incidenceDart_negative_source component quartet d hds,
      incidenceDart_negative_source component quartet e hes, hdi, hej, hq])
  exact hdi.symm.trans ((congrArg (incidenceDartLabel component quartet) hde).trans hej)

theorem incidenceCycle_quartet_support_card_le_two {L C Q : Type*}
    [Fintype L] [DecidableEq L] [DecidableEq Q]
    (component : L → C) (quartet : L → Q) {v : C ⊕ Q}
    (w : (incidenceGraph component quartet).Walk v v) (hw : w.IsCycle) (q : Q) :
    (Finset.univ.filter (fun i => quartet i = q ∧ incidenceWalkSign component quartet w i ≠ 0)).card ≤ 2 := by
  let s := Finset.univ.filter (fun i => quartet i = q ∧ incidenceWalkSign component quartet w i = 1)
  let t := Finset.univ.filter (fun i => quartet i = q ∧ incidenceWalkSign component quartet w i = -1)
  have hs : s.card ≤ 1 := Finset.card_le_one.mpr (by
    intro i hi j hj
    obtain ⟨hiQ, hiS⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨hjQ, hjS⟩ := (Finset.mem_filter.mp hj).2
    exact incidenceCycle_positive_unique component quartet w hw i j hiS hjS (hiQ.trans hjQ.symm))
  have ht : t.card ≤ 1 := Finset.card_le_one.mpr (by
    intro i hi j hj
    obtain ⟨hiQ, hiS⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨hjQ, hjS⟩ := (Finset.mem_filter.mp hj).2
    exact incidenceCycle_negative_unique component quartet w hw i j hiS hjS (hiQ.trans hjQ.symm))
  have hsub : Finset.univ.filter (fun i => quartet i = q ∧ incidenceWalkSign component quartet w i ≠ 0) ⊆ s ∪ t := by
    intro i hi
    obtain ⟨hiq, hin⟩ := (Finset.mem_filter.mp hi).2
    rcases incidenceWalkSign_values component quartet w hw.isTrail i with h0 | h1 | hm
    · exact (hin h0).elim
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiq, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiq, hm⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

theorem exists_balancedIncidenceCycle {L C Q : Type*}
    [Fintype L] [Fintype C] [Fintype Q] [Nonempty L]
    [DecidableEq L] [DecidableEq C] [DecidableEq Q]
    (component : L → C) (quartet : L → Q)
    (hcard : Fintype.card C + Fintype.card Q ≤ Fintype.card L) :
    Nonempty (BalancedIncidenceCycle component quartet) := by
  rcases incidence_parallel_or_cycle component quartet hcard with ⟨i, j, hij, hc, hq⟩ | ⟨v, w, hw⟩
  · refine ⟨{
      sign := parallelCycleSign i j
      nonzero := ⟨i, Or.inl (parallelCycleSign_left i j hij)⟩
      values := ?_
      component_balanced := parallelCycleSign_balanced component i j hc
      quartet_balanced := parallelCycleSign_balanced quartet i j hq
      quartet_support := ?_
    }⟩
    · intro k
      by_cases hki : k = i
      · subst k; exact Or.inr (Or.inl (parallelCycleSign_left i j hij))
      by_cases hkj : k = j
      · subst k; exact Or.inr (Or.inr (parallelCycleSign_right i j hij))
      exact Or.inl (parallelCycleSign_other i j k hki hkj)
    · intro q
      have hsub : Finset.univ.filter (fun k => quartet k = q ∧ parallelCycleSign i j k ≠ 0) ⊆ {i, j} := by
        intro k hk
        have hn := (Finset.mem_filter.mp hk).2.2
        by_cases hki : k = i
        · simp [hki]
        by_cases hkj : k = j
        · simp [hkj]
        exact (hn (parallelCycleSign_other i j k hki hkj)).elim
      exact (Finset.card_le_card hsub).trans (by simp [hij])
  · exact ⟨{
      sign := incidenceWalkSign component quartet w
      nonzero := incidenceCycleSign_nonzero component quartet w hw
      values := incidenceWalkSign_values component quartet w hw.isTrail
      component_balanced := incidenceWalkSign_component_balanced component quartet w
      quartet_balanced := incidenceWalkSign_quartet_balanced component quartet w
      quartet_support := incidenceCycle_quartet_support_card_le_two component quartet w hw
    }⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetIndexCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf coordinates within a labeled bottom quartet -/

namespace Ostmann

open scoped BigOperators

theorem sum_bottomQuartet_fiber {R : Type*} [AddCommMonoid R] (n : ℕ)
    (q : TreeLeafIndex n) (f : TreeLeafIndex (n + 2) → R) :
    (∑ j ∈ Finset.univ.filter (fun j => bottomQuartet n j = q), f j) =
      ∑ j : TreeLeafIndex 2, f (quartetLeafIndex n q j) := by
  classical
  have h := (quartetIndexFiberEquiv n q).symm.sum_comp
    (fun j : {j : TreeLeafIndex (n + 2) // bottomQuartet n j = q} => f j.1)
  change (∑ j : TreeLeafIndex 2, f (quartetLeafIndex n q j)) =
    ∑ j : {j : TreeLeafIndex (n + 2) // bottomQuartet n j = q}, f j.1 at h
  rw [h]
  exact Finset.sum_subtype _ (by simp) f

theorem sum_four_treeLeaves {R : Type*} [AddCommMonoid R] (f : TreeLeafIndex 2 → R) :
    (∑ i : TreeLeafIndex 2, f i) =
      (f (.inl (.inl ())) + f (.inl (.inr ()))) +
        (f (.inr (.inl ())) + f (.inr (.inr ()))) := by
  calc
    _ = (∑ i : Unit ⊕ Unit, f (.inl i)) + ∑ i : Unit ⊕ Unit, f (.inr i) :=
      Fintype.sum_sum_type f
    _ = _ := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Fintype.sum_unique]
      congr 5

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetSignClassification
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Classifying a balanced action supported on at most two quartet leaves -/

namespace Ostmann

theorem quartetSign_classification (a b c d : ℤ)
    (ha : a = 0 ∨ a = 1 ∨ a = -1) (hb : b = 0 ∨ b = 1 ∨ b = -1)
    (hc : c = 0 ∨ c = 1 ∨ c = -1) (hd : d = 0 ∨ d = 1 ∨ d = -1)
    (hsum : a + b + c + d = 0)
    (hcard : (if a = 0 then (0 : ℕ) else 1) + (if b = 0 then 0 else 1) +
      (if c = 0 then 0 else 1) + (if d = 0 then 0 else 1) ≤ 2) :
    ∃ choice : QuartetMovingCase, ∃ δ : ℤ,
      (δ = 0 ∨ δ = 1 ∨ δ = -1) ∧
      (((a, b), (c, d)) : (ℤ × ℤ) × (ℤ × ℤ)) =
        treeLeafMap (fun s : ℤ => δ * s) 2 (quartetMovingSign choice) := by
  rcases ha with ha | ha | ha
  all_goals rcases hb with hb | hb | hb
  all_goals rcases hc with hc | hc | hc
  all_goals rcases hd with hd | hd | hd
  all_goals simp only [ha, hb, hc, hd] at hsum hcard ⊢
  all_goals norm_num at hsum
  all_goals norm_num at hcard
  all_goals first
    | exact ⟨.leftPair, 0, by decide, by decide⟩
    | exact ⟨.leftPair, 1, by decide, by decide⟩
    | exact ⟨.leftPair, -1, by decide, by decide⟩
    | exact ⟨.rightPair, 1, by decide, by decide⟩
    | exact ⟨.rightPair, -1, by decide, by decide⟩
    | exact ⟨.cross true true, 1, by decide, by decide⟩
    | exact ⟨.cross true true, -1, by decide, by decide⟩
    | exact ⟨.cross true false, 1, by decide, by decide⟩
    | exact ⟨.cross true false, -1, by decide, by decide⟩
    | exact ⟨.cross false true, 1, by decide, by decide⟩
    | exact ⟨.cross false true, -1, by decide, by decide⟩
    | exact ⟨.cross false false, 1, by decide, by decide⟩
    | exact ⟨.cross false false, -1, by decide, by decide⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetCycleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph cycle supplies genuine quartet coordinate signs -/

namespace Ostmann

open scoped BigOperators

theorem sum_zero_indicator_eq_card {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℤ) :
    (∑ i ∈ s, if f i = 0 then (0 : ℕ) else 1) = (s.filter fun i => f i ≠ 0).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : f i = 0 <;> simp [h]

theorem balanced_quartet_coordinates (n : ℕ) (sign : TreeLeafIndex (n + 2) → ℤ)
    (hvalues : ∀ j, sign j = 0 ∨ sign j = 1 ∨ sign j = -1)
    (hbalance : ∀ q, (∑ j ∈ Finset.univ.filter (fun j => bottomQuartet n j = q), sign j) = 0)
    (hsupport : ∀ q,
      (Finset.univ.filter (fun j => bottomQuartet n j = q ∧ sign j ≠ 0)).card ≤ 2) :
    ∃ choice : TreeLeafIndex n → QuartetMovingCase, ∃ δ : TreeLeafIndex n → ℤ,
      (∀ q, δ q = 0 ∨ δ q = 1 ∨ δ q = -1) ∧
      ∀ q j, sign (quartetLeafIndex n q j) =
        treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j := by
  classical
  have hlocal (q : TreeLeafIndex n) :
      ∃ choice : QuartetMovingCase, ∃ δ : ℤ, (δ = 0 ∨ δ = 1 ∨ δ = -1) ∧
        ∀ j, sign (quartetLeafIndex n q j) =
          treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ * s) 2 (quartetMovingSign choice)) j := by
    let f : TreeLeafIndex 2 → ℤ := fun j => sign (quartetLeafIndex n q j)
    have hsum : (∑ j : TreeLeafIndex 2, f j) = 0 := by
      rw [← sum_bottomQuartet_fiber]
      exact hbalance q
    have hcard : (∑ j : TreeLeafIndex 2, if f j = 0 then (0 : ℕ) else 1) ≤ 2 := by
      rw [← sum_bottomQuartet_fiber n q (fun j => if sign j = 0 then (0 : ℕ) else 1),
        sum_zero_indicator_eq_card, Finset.filter_filter]
      exact hsupport q
    rw [sum_four_treeLeaves] at hsum hcard
    obtain ⟨moving, δ, hδ, heq⟩ := quartetSign_classification
      (f (.inl (.inl ()))) (f (.inl (.inr ())))
      (f (.inr (.inl ()))) (f (.inr (.inr ())))
      (hvalues _) (hvalues _) (hvalues _) (hvalues _) (by omega) (by simpa only [Nat.add_assoc] using hcard)
    refine ⟨moving, δ, hδ, ?_⟩
    intro j
    have h := congrArg (fun m : TreeLeafTuple ℤ 2 => treeLeafTupleEquiv ℤ 2 m j) heq
    rcases j with (⟨⟩ | ⟨⟩) | (⟨⟩ | ⟨⟩) <;> exact h
  choose choice δ hδ hcoord using hlocal
  exact ⟨choice, δ, hδ, hcoord⟩

theorem BalancedIncidenceCycle.quartet_coordinates {C : Type*} [DecidableEq C]
    (n : ℕ) {component : TreeLeafIndex (n + 2) → C}
    (cycle : BalancedIncidenceCycle component (bottomQuartet n)) :
    ∃ choice : TreeLeafIndex n → QuartetMovingCase, ∃ δ : TreeLeafIndex n → ℤ,
      (∀ q, δ q = 0 ∨ δ q = 1 ∨ δ q = -1) ∧
      (∀ q j, cycle.sign (quartetLeafIndex n q j) =
        treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j) ∧
      ∃ q, δ q = 1 ∨ δ q = -1 := by
  obtain ⟨choice, δ, hδ, hcoord⟩ := balanced_quartet_coordinates n cycle.sign
    cycle.values cycle.quartet_balanced cycle.quartet_support
  refine ⟨choice, δ, hδ, hcoord, ?_⟩
  obtain ⟨j, hj⟩ := cycle.nonzero
  let q := (quartetLeafCoordinates n j).1
  have hn : δ q ≠ 0 := by
    intro hz
    have h := hcoord q (quartetLeafCoordinates n j).2
    rw [treeLeafTupleEquiv_map, hz, zero_mul] at h
    have hi := quartetLeafIndex_coordinates n j
    change quartetLeafIndex n q (quartetLeafCoordinates n j).2 = j at hi
    rw [hi] at h
    rcases hj with hj | hj <;> omega
  exact ⟨q, (hδ q).resolve_left hn⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_FiberProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correlation over paired finite fibers

The component totals determine equal-cardinality fibers. Cauchy--Schwarz
on their sums, together with invariance under a cycle action, gives the
finite projection reduction before the local quartet bounds are applied.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem complex_correlation_sq_le {Ω : Type*} [Fintype Ω] (f g : Ω → ℂ) :
    ‖∑ x : Ω, f x * conj (g x)‖ ^ 2 ≤
      (∑ x : Ω, ‖f x‖ ^ 2) * ∑ x : Ω, ‖g x‖ ^ 2 := by
  have hn : ‖∑ x : Ω, f x * conj (g x)‖ ≤ ∑ x : Ω, ‖f x‖ * ‖g x‖ := by
    simpa only [norm_mul, Complex.norm_conj] using
      norm_sum_le (Finset.univ : Finset Ω) (fun x => f x * conj (g x))
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x : Ω => ‖f x‖) (fun x => ‖g x‖)
  have hnn : 0 ≤ ∑ x : Ω, ‖f x‖ * ‖g x‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs

/-- A common fiber-size bound controls the energy of the fiber sums. -/
theorem fiberSum_energy_le {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]
    (τ : Ω → T) (f : Ω → ℂ) (N : ℕ)
    (hN : ∀ t, (Finset.univ.filter (fun x => τ x = t)).card ≤ N) :
    (∑ t : T, ‖fiberSum τ f t‖ ^ 2) ≤ (N : ℝ) * ∑ x : Ω, ‖f x‖ ^ 2 := by
  have ht (t : T) : ‖fiberSum τ f t‖ ^ 2 ≤
      (N : ℝ) * ∑ x ∈ Finset.univ.filter (fun x => τ x = t), ‖f x‖ ^ 2 := by
    have h := complex_weighted_sum_sq (Finset.univ.filter (fun x => τ x = t))
      (fun _ => 1) f
    simp only [Complex.ofReal_one, one_mul, one_pow, Finset.sum_const, nsmul_eq_mul,
      mul_one] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN t)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc
    _ ≤ ∑ t : T, (N : ℝ) *
        ∑ x ∈ Finset.univ.filter (fun x => τ x = t), ‖f x‖ ^ 2 := Finset.sum_le_sum fun t _ => ht t
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) (fun x => ‖f x‖ ^ 2)

/-- A fiber-preserving finite action does not change the fiber sums. -/
theorem fiberSum_actionAverage {G Ω T : Type*} [Group G] [Fintype G]
    [Fintype Ω] [DecidableEq T] [MulAction G Ω]
    (τ : Ω → T) (hτ : ∀ (g : G) x, τ (g • x) = τ x) (f : Ω → ℂ) (t : T) :
    fiberSum τ (finiteActionAverage (G := G) f) t = fiberSum τ f t := by
  have h := finiteActionAverage_correlation (G := G) f
    (fun x => if τ x = t then 1 else 0) (by intro g x; rw [hτ])
  simpa only [apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero,
    fiberSum, Finset.sum_filter] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ComponentFibers
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform product fibers for a nonempty component

Fixing one distinguished leaf identifies every component-product fiber
with independent values on the remaining leaves. The fiber cardinality
therefore does not depend on its total.
-/

namespace Ostmann

open scoped BigOperators

theorem card_componentProduct {I G : Type*} [Fintype I] [DecidableEq I]
    [CommGroup G] [Fintype G] [DecidableEq G] (i₀ : I) (P : G) :
    Fintype.card {m : I → G // ∏ i, m i = P} =
      (Fintype.card G) ^ Fintype.card {i : I // i ≠ i₀} := by
  rw [Fintype.card_congr (componentProductEquiv i₀ P), Fintype.card_fun]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PartitionProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous product fibers for an arbitrary partition of the leaves -/

namespace Ostmann

open scoped BigOperators

theorem sum_card_partition {L C : Type*} [Fintype L] [Fintype C]
    [DecidableEq C] (component : L → C) :
    (∑ c : C, Fintype.card {i : L // component i = c}) = Fintype.card L := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv component)

theorem card_partitionProductFiber {L C G : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (component : L → C) (pivot : ∀ c, {i : L // component i = c}) (P : C → G) :
    Fintype.card {m : L → G // partitionProduct component m = P} =
      Fintype.card G ^ (Fintype.card L - Fintype.card C) := by
  classical
  rw [Fintype.card_congr (partitionProductFiberEquiv component P), Fintype.card_pi]
  have hcard (c : C) :
      Fintype.card {i : {i : L // component i = c} // i ≠ pivot c} =
        Fintype.card {i : L // component i = c} - 1 := by
    simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp_rw [card_componentProduct (pivot _), hcard]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_tsub_distrib]
  · simp only [sum_card_partition, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Nat.cast_id]
  · intro c _
    exact Fintype.card_pos_iff.mpr ⟨pivot c⟩

theorem card_partitionProduct_filter {L C G : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (component : L → C) (pivot : ∀ c, {i : L // component i = c}) (P : C → G) :
    (Finset.univ.filter fun m : L → G => partitionProduct component m = P).card =
      Fintype.card G ^ (Fintype.card L - Fintype.card C) := by
  rw [← Fintype.card_subtype]
  exact card_partitionProductFiber component pivot P

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairedPartitions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection reduction for two different partitions of the leaves -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem card_pairedMaps {Ω₁ Ω₂ T : Type*}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq T]
    (τ₁ : Ω₁ → T) (τ₂ : Ω₂ → T) (N : ℕ)
    (hN : ∀ t, (Finset.univ.filter (fun y => τ₂ y = t)).card = N) :
    (Finset.univ.filter fun xy : Ω₁ × Ω₂ => τ₁ xy.1 = τ₂ xy.2).card =
      Fintype.card Ω₁ * N := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  have hy (x : Ω₁) : (∑ y : Ω₂, if τ₁ x = τ₂ y then 1 else 0) = N := by
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter, eq_comm] using hN (τ₁ x)
  simp only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem pairedMaps_correlation_eq {Ω₁ Ω₂ T : Type*}
    [Fintype Ω₁] [Fintype Ω₂] [Fintype T] [DecidableEq T]
    (τ₁ : Ω₁ → T) (τ₂ : Ω₂ → T) (f : Ω₁ → ℂ) (g : Ω₂ → ℂ) :
    (∑ t : T, fiberSum τ₁ f t * conj (fiberSum τ₂ g t)) =
      ∑ x : Ω₁, ∑ y : Ω₂, if τ₁ x = τ₂ y then f x * conj (g y) else 0 := by
  unfold fiberSum
  simp only [Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  simp only [map_sum, apply_ite, map_zero, Finset.mul_sum, mul_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : τ₁ x = τ₂ y
  · simp [hxy]
  · simp [hxy, Ne.symm hxy]

theorem pairedMaps_correlation_sq_le {G Ω₁ Ω₂ T : Type*}
    [Group G] [Fintype G] [Fintype Ω₁] [Fintype Ω₂] [Fintype T]
    [DecidableEq T] [MulAction G Ω₁]
    (τ₁ : Ω₁ → T) (τ₂ : Ω₂ → T) (hτ : ∀ (z : G) x, τ₁ (z • x) = τ₁ x)
    (f : Ω₁ → ℂ) (g : Ω₂ → ℂ) (N : ℕ)
    (hN₁ : ∀ t, (Finset.univ.filter (fun x => τ₁ x = t)).card ≤ N)
    (hN₂ : ∀ t, (Finset.univ.filter (fun x => τ₂ x = t)).card ≤ N) :
    ‖∑ x : Ω₁, ∑ y : Ω₂, if τ₁ x = τ₂ y then f x * conj (g y) else 0‖ ^ 2 ≤
      (N : ℝ) ^ 2 * (∑ x : Ω₁, ‖finiteActionAverage (G := G) f x‖ ^ 2) *
        ∑ y : Ω₂, ‖g y‖ ^ 2 := by
  rw [← pairedMaps_correlation_eq]
  have hF := fiberSum_energy_le τ₁ (finiteActionAverage (G := G) f) N hN₁
  have hG := fiberSum_energy_le τ₂ g N hN₂
  have h := complex_correlation_sq_le
    (fiberSum τ₁ (finiteActionAverage (G := G) f)) (fiberSum τ₂ g)
  simp_rw [fiberSum_actionAverage τ₁ hτ f] at h hF
  apply h.trans
  have hb := mul_le_mul hF hG (by positivity) (by positivity)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem partitionProduct_cycleMultiply {L C G : Type*}
    [Fintype L] [DecidableEq C] [CommGroup G]
    (component : L → C) (sign : L → ℤ)
    (hs : ∀ c, ∑ i ∈ Finset.univ.filter (fun i => component i = c), sign i = 0)
    (z : G) (m : L → G) :
    partitionProduct component (cycleMultiply sign z m) = partitionProduct component m := by
  classical
  funext c
  unfold partitionProduct
  have hprod (f : L → G) : (∏ i : {i : L // component i = c}, f i.1) =
      ∏ i ∈ Finset.univ.filter (fun i => component i = c), f i :=
    (Finset.prod_subtype _ (by simp) f).symm
  rw [hprod, hprod]
  exact cycleMultiply_preserves_product _ sign (hs c) z m

/-- Exact counting normalization of the paired-component projection step. -/
theorem pairedPartitions_projection {L C G : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (component₁ component₂ : L → C)
    (pivot₁ : ∀ c, {i : L // component₁ i = c})
    (pivot₂ : ∀ c, {i : L // component₂ i = c})
    (sign : L → ℤ)
    (hs : ∀ c, ∑ i ∈ Finset.univ.filter (fun i => component₁ i = c), sign i = 0)
    (f g : (L → G) → ℂ) :
    ‖((Fintype.card (L → G) : ℂ) *
        (Fintype.card G ^ (Fintype.card L - Fintype.card C) : ℕ))⁻¹ *
      (∑ x : L → G, ∑ y : L → G,
        if partitionProduct component₁ x = partitionProduct component₂ y
        then f x * conj (g y) else 0)‖ ^ 2 ≤
      ((∑ x : L → G, ‖cycleAverage sign f x‖ ^ 2) / (Fintype.card (L → G) : ℝ)) *
        ((∑ y : L → G, ‖g y‖ ^ 2) / (Fintype.card (L → G) : ℝ)) := by
  let := leafCycleAction (G := G) sign
  let N := Fintype.card G ^ (Fintype.card L - Fintype.card C)
  have hN : 0 < N := pow_pos Fintype.card_pos _
  have hL : (Fintype.card (L → G) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have h := pairedMaps_correlation_sq_le (G := G)
    (partitionProduct component₁) (partitionProduct component₂)
    (partitionProduct_cycleMultiply component₁ sign hs) f g N
    (fun P => (card_partitionProduct_filter component₁ pivot₁ P).le)
    (fun P => (card_partitionProduct_filter component₂ pivot₂ P).le)
  change ‖((Fintype.card (L → G) : ℂ) * (N : ℂ))⁻¹ * _‖ ^ 2 ≤ _
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast, mul_pow]
  have hscaled := mul_le_mul_of_nonneg_left h
    (sq_nonneg (((Fintype.card (L → G) : ℝ) * (N : ℝ))⁻¹))
  change _ ≤ _ * ((↑N ^ 2 * ∑ x, ‖cycleAverage sign f x‖ ^ 2) * ∑ y, ‖g y‖ ^ 2) at hscaled
  convert hscaled using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PairedRationalReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cycle projection for two actual rational diagrams -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The counting denominator is exactly the size of the equal-total sample space. -/
theorem card_pairedPartitions {L C G : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    [CommGroup G] [Fintype G] [DecidableEq G]
    (component₁ component₂ : L → C)
    (pivot₂ : ∀ c, {i : L // component₂ i = c}) :
    (Finset.univ.filter fun xy : (L → G) × (L → G) =>
      partitionProduct component₁ xy.1 = partitionProduct component₂ xy.2).card =
        Fintype.card (L → G) * Fintype.card G ^ (Fintype.card L - Fintype.card C) :=
  card_pairedMaps _ _ _ (card_partitionProduct_filter component₂ pivot₂)

/-- The projection reduction in `tree-projection-reduction`, for the actual diagram values. -/
theorem pairedRationalTree_projection {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (n : ℕ) {C : Type*} [Fintype C] [DecidableEq C]
    (component₁ component₂ : TreeLeafIndex (n + 2) → C)
    (pivot₁ : ∀ c, {i : TreeLeafIndex (n + 2) // component₁ i = c})
    (pivot₂ : ∀ c, {i : TreeLeafIndex (n + 2) // component₂ i = c})
    (hc : Fintype.card C ≤ 3 * 2 ^ n)
    (D₁ D₂ : (ZMod p)ˣ) {K₁ K₂ : (ZMod p)ˣ}
    (T₁ : RationalTreeData (ZMod p)ˣ (n + 2) K₁)
    (T₂ : RationalTreeData (ZMod p)ˣ (n + 2) K₂)
    (XL₁ XR₁ XL₂ XR₂ : (ZMod p)ˣ) (c₁ c₂ : TreeLeafTuple Bool (n + 2)) :
    let W₁ := indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁
    let W₂ := indexedRationalAmplitude g D₂ T₂ XL₂ XR₂ c₂
    ∃ cycle : BalancedIncidenceCycle component₁ (bottomQuartet n),
      ‖pairedPartitionCorrelation component₁ component₂ W₁ W₂‖ ^ 2 ≤
        (3 : ℝ) ^ (2 ^ (n + 2)) *
          ((∑ m : TreeLeafIndex (n + 2) → (ZMod p)ˣ,
            ‖cycleAverage cycle.sign W₁ m‖ ^ 2) /
              (Fintype.card (TreeLeafIndex (n + 2) → (ZMod p)ˣ) : ℝ)) := by
  dsimp only
  have hcard : Fintype.card C + Fintype.card (TreeLeafIndex n) ≤
      Fintype.card (TreeLeafIndex (n + 2)) := by
    rw [card_treeLeafIndex, card_treeLeafIndex, pow_add]
    norm_num
    omega
  obtain ⟨cycle⟩ := exists_balancedIncidenceCycle component₁ (bottomQuartet n) hcard
  refine ⟨cycle, ?_⟩
  have h := pairedPartitions_projection component₁ component₂ pivot₁ pivot₂ cycle.sign
    cycle.component_balanced (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁)
      (indexedRationalAmplitude g D₂ T₂ XL₂ XR₂ c₂)
  apply h.trans
  have hsecond := indexedRationalAmplitude_l2_bound hp g hg henergy D₂ T₂ XL₂ XR₂ c₂
  have hfirst : 0 ≤
      (∑ m : TreeLeafIndex (n + 2) → (ZMod p)ˣ,
        ‖cycleAverage cycle.sign (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁) m‖ ^ 2) /
          (Fintype.card (TreeLeafIndex (n + 2) → (ZMod p)ˣ) : ℝ) := by positivity
  exact (mul_le_mul_of_nonneg_left hsecond hfirst).trans_eq (mul_comm _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative paired comparison for the actual rational diagrams

This assembles the graph cycle, all six local quartet estimates, exact
product-fiber coordinates, and horizontal density domination. The error
is explicit; no tree-comparison theorem is taken as an input.
-/

namespace Ostmann

open scoped BigOperators

theorem pairedRationalTree_comparison {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (n : ℕ) {C : Type*} [Fintype C] [DecidableEq C]
    (component₁ component₂ : TreeLeafIndex (n + 2) → C)
    (pivot₁ : ∀ c, {i : TreeLeafIndex (n + 2) // component₁ i = c})
    (pivot₂ : ∀ c, {i : TreeLeafIndex (n + 2) // component₂ i = c})
    (hc : Fintype.card C ≤ 3 * 2 ^ n)
    (D₁ D₂ : (ZMod p)ˣ) {K₁ K₂ : (ZMod p)ˣ}
    (T₁ : RationalTreeData (ZMod p)ˣ (n + 2) K₁)
    (T₂ : RationalTreeData (ZMod p)ˣ (n + 2) K₂)
    (XL₁ XR₁ XL₂ XR₂ : (ZMod p)ˣ) (c₁ c₂ : TreeLeafTuple Bool (n + 2))
    (cL cR : TreeLeafIndex n → Bool)
    (hconj : ∀ q, quartetBlockEquiv Bool n c₁ q = ((cL q, !(cL q)), (cR q, !(cR q)))) :
    ‖pairedPartitionCorrelation component₁ component₂
      (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁)
      (indexedRationalAmplitude g D₂ T₂ XL₂ XR₂ c₂)‖ ^ 2 ≤
      (3 : ℝ) ^ (2 ^ (n + 2)) * ((2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1))) := by
  obtain ⟨cycle, hcycle⟩ := pairedRationalTree_projection hp g hg henergy n
    component₁ component₂ pivot₁ pivot₂ hc D₁ D₂ T₁ T₂ XL₁ XR₁ XL₂ XR₂ c₁ c₂
  obtain ⟨choice, δ, _, hsign, i, hi⟩ := cycle.quartet_coordinates n
  have hmean := projectedTree_mean_le g hg henergy ε hε hflat D₁ n T₁ XL₁ XR₁ c₁
    cL cR hconj choice cycle.sign δ hsign i hi
  have hindexed :
      (∑ m : TreeLeafIndex (n + 2) → (ZMod p)ˣ,
        ‖cycleAverage cycle.sign (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁) m‖ ^ 2) /
        (Fintype.card (TreeLeafIndex (n + 2) → (ZMod p)ˣ) : ℝ) ≤
      (2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1)) := by
    rw [← (treeLeafTupleEquiv (ZMod p)ˣ (n + 2)).sum_comp
      (fun m => ‖cycleAverage cycle.sign (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁) m‖ ^ 2),
      ← Fintype.card_congr (treeLeafTupleEquiv (ZMod p)ˣ (n + 2))]
    exact hmean
  exact hcycle.trans (mul_le_mul_of_nonneg_left hindexed (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeComparisonError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A prime-uniform bound for the explicit quartet error -/

namespace Ostmann

private theorem two_bad_error_polynomial_le (C r x t : ℝ)
    (hC : 0 ≤ C) (hC2 : C ≤ 2) (hr1 : r ≤ 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    4 * r * C ^ 3 * t + 3 * r * x * C ^ 4 + 4 * x * C ^ 3 +
      (C * t + x * C) ^ 2 * (C ^ 2 * t) ≤ 96 * t + 80 * x := by
  have hc3 : C ^ 3 ≤ (2 : ℝ) ^ 3 := by gcongr
  have hc4 : C ^ 4 ≤ (2 : ℝ) ^ 4 := by gcongr
  have hbase : C * t + x * C ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) * 1 + 1 * 2 := by gcongr
      _ = 4 := by norm_num
  have h1 : 4 * r * C ^ 3 * t ≤ 32 * t := by
    calc
      _ ≤ 4 * 1 * (2 : ℝ) ^ 3 * t := by gcongr
      _ = _ := by ring
  have h2 : 3 * r * x * C ^ 4 ≤ 48 * x := by
    calc
      _ ≤ 3 * 1 * x * (2 : ℝ) ^ 4 := by gcongr
      _ = _ := by ring
  have h3 : 4 * x * C ^ 3 ≤ 32 * x := by
    calc
      _ ≤ 4 * x * (2 : ℝ) ^ 3 := by gcongr
      _ = _ := by ring
  have h4 : (C * t + x * C) ^ 2 * (C ^ 2 * t) ≤ 64 * t := by
    calc
      _ ≤ (4 : ℝ) ^ 2 * (2 ^ 2 * t) := by gcongr
      _ = _ := by ring
  linarith

private theorem local_error_polynomial_le (C r x t s : ℝ)
    (hC : 0 ≤ C) (hC2 : C ≤ 2) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hxs : x ≤ s) :
    16 * C ^ 5 * t + 16 * C ^ 3 *
      (2 * C ^ 2 * (t ^ 2 + s) +
        (4 * r * C ^ 3 * t + 3 * r * x * C ^ 4 + 4 * x * C ^ 3 +
          (C * t + x * C) ^ 2 * (C ^ 2 * t))) ≤ 16384 * (t + s) := by
  have hb := two_bad_error_polynomial_le C r x t hC hC2 hr1 hx hx1 ht ht1
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have hf : 2 * C ^ 2 * (t ^ 2 + s) ≤ 8 * (t + s) := by
    calc
      _ ≤ 2 * (2 : ℝ) ^ 2 * (t + s) := by gcongr
      _ = _ := by ring
  have hsum : 2 * C ^ 2 * (t ^ 2 + s) +
      (4 * r * C ^ 3 * t + 3 * r * x * C ^ 4 + 4 * x * C ^ 3 +
        (C * t + x * C) ^ 2 * (C ^ 2 * t)) ≤ 104 * t + 88 * s := by linarith
  calc
    _ ≤ 16 * (2 : ℝ) ^ 5 * t + 16 * 2 ^ 3 * (104 * t + 88 * s) := by gcongr
    _ ≤ _ := by nlinarith

theorem quartetLocalMeanError_le {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    quartetLocalMeanError p ε ≤ 16384 * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) := by
  let U : ℝ := Fintype.card (ZMod p)ˣ
  let C : ℝ := (p : ℝ) / U
  let r : ℝ := U / p
  let x : ℝ := (p : ℝ)⁻¹
  let t : ℝ := ε ^ 2
  let s : ℝ := Real.sqrt (3 / (p : ℝ))
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hU : U = (p : ℝ) - 1 := by
    dsimp [U]
    rw [ZMod.card_units, Nat.cast_sub (by omega), Nat.cast_one]
  have hU0 : 0 < U := by linarith
  have hC : 0 ≤ C := div_nonneg hp0.le hU0.le
  have hC2 : C ≤ 2 := (div_le_iff₀ hU0).mpr (by linarith)
  have hr : 0 ≤ r := div_nonneg hU0.le hp0.le
  have hr1 : r ≤ 1 := (div_le_iff₀ hp0).mpr (by linarith)
  have hx : 0 ≤ x := inv_nonneg.mpr hp0.le
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (inv_le_one₀ hp0).mpr (by linarith)
  have ht : 0 ≤ t := sq_nonneg ε
  have ht1 : t ≤ 1 := by dsimp [t]; nlinarith
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 3 * x := by
    dsimp [s, x]
    rw [Real.sq_sqrt (div_nonneg (by norm_num) hp0.le)]
    rfl
  have hxs : x ≤ s := by nlinarith [sq_nonneg (s - x)]
  have h := local_error_polynomial_le C r x t s hC hC2 hr hr1 hx hx1 ht ht1 hs hxs
  dsimp [C, r, x, t, s] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [quartetLocalMeanError, friendlyQuartetError, twoBadQuartetError, U, div_eq_mul_inv]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetTreeSmallParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform small parameters for the actual quartet tree error -/

namespace Ostmann

theorem quartetTreeConstant_pos (n : ℕ) : 0 < quartetTreeConstant n := by
  unfold quartetTreeConstant
  positivity

theorem quartetTree_error_le {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (3 : ℝ) ^ (2 ^ (n + 2)) * ((2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
      (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1))) ≤
    quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hu : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (by omega), Nat.cast_one]
  have hratio : (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ 2 := by
    rw [hu]
    exact (div_le_iff₀ (by linarith : 0 < (p : ℝ) - 1)).mpr (by linarith)
  have hr0 : 0 ≤ (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) := by positivity
  have hb : 8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 ≤ 128 := by
    have h : ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 ≤ 16 := by
      calc
        _ ≤ (2 : ℝ) ^ 4 := pow_le_pow_left₀ hr0 hratio 4
        _ = 16 := by norm_num
    linarith
  calc
    _ ≤ (3 : ℝ) ^ (2 ^ (n + 2)) * ((2 : ℝ) ^ (2 ^ n - 1) *
        ((16384 * (ε ^ 2 + Real.sqrt (3 / (p : ℝ)))) * (128 : ℝ) ^ (2 ^ n - 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (quartetLocalMeanError_le hp ε hε hε1)
        (pow_le_pow_left₀ (by positivity) hb _) (by positivity) (by positivity)
    _ = _ := by unfold quartetTreeConstant; ring

theorem exists_quartet_small_parameters (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ p : ℕ, N ≤ p → K * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) ≤ δ ^ 2 := by
  let t := min 1 (δ ^ 2 / (2 * K))
  have ht : 0 < t := lt_min (by norm_num) (div_pos (sq_pos_of_pos hδ) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htδ : 2 * K * t ≤ δ ^ 2 := by
    have htl : t ≤ δ ^ 2 / (2 * K) := min_le_right _ _
    have h := (le_div_iff₀ (by positivity : 0 < 2 * K)).mp htl
    nlinarith
  refine ⟨Real.sqrt t, Real.sqrt_pos.2 ht, ?_, max 3 ⌈3 / t ^ 2⌉₊, le_max_left _ _, ?_⟩
  · exact (Real.sqrt_le_one).mpr ht1
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (le_max_left 3 ⌈3 / t ^ 2⌉₊).trans hp
    have hp0 : (0 : ℝ) < p := by linarith
    have hpt : 3 / t ^ 2 ≤ (p : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hp))
    have hdiv : 3 / (p : ℝ) ≤ t ^ 2 := by
      apply (div_le_iff₀ hp0).mpr
      have h := (div_le_iff₀ (sq_pos_of_pos ht)).mp hpt
      nlinarith
    have hsqrt : Real.sqrt (3 / (p : ℝ)) ≤ t := (Real.sqrt_le_iff).mpr ⟨ht.le, hdiv⟩
    rw [Real.sq_sqrt ht.le]
    nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ArrangementGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bipartite overlap graph of an actual bulk permutation -/

namespace Ostmann

open scoped Classical

theorem arrangementRight_surjective {L : Type*} {m : ℕ} (hm : 0 < m)
    (e : Equiv.Perm (L × Fin m)) : Function.Surjective (arrangementRight e) := by
  intro c
  obtain ⟨l, rfl⟩ := arrangementLeft_surjective hm e c
  exact ⟨(e (l, ⟨0, hm⟩)).1, arrangement_components_match e (l, ⟨0, hm⟩)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_UniformHomAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite group samples push forward uniformly through a homomorphism -/

namespace Ostmann
open scoped Classical BigOperators

theorem uniform_hom_average {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f) (F : B → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * (∑ a, F (f a)) =
      (Fintype.card B : ℂ)⁻¹ * ∑ b, F b := by
  have hcard (b : B) : Fintype.card {a : A // f a = b} = Fintype.card f.ker :=
    Fintype.card_congr (f.fiberEquivKerOfSurjective hf b)
  have htotal : Fintype.card A = Fintype.card B * Fintype.card f.ker := by
    calc
      _ = Fintype.card (Σ b : B, {a : A // f a = b}) :=
        (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
      _ = _ := by simp only [Fintype.card_sigma, hcard, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.cast_id]
  have hsum : (∑ a, F (f a)) = (Fintype.card f.ker : ℂ) * ∑ b, F b := by
    rw [← Fintype.sum_fiberwise f (fun a => F (f a))]
    simp only [show ∀ b (a : {a : A // f a = b}), F (f a.val) = F b from
      fun _ a => congrArg F a.property, Finset.sum_const, Finset.card_univ,
      hcard, nsmul_eq_mul, ← Finset.mul_sum]
  rw [hsum, htotal, Nat.cast_mul]
  have hK : (Fintype.card f.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ArrangementUniformLaw
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact joint law of the two actual bulk leaf products -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem arrangementProductMap_range_card {L G : Type*} [Fintype L] [CommGroup G]
    [Fintype G] {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) :
    Fintype.card (arrangementProductMap (G := G) e).range =
      Fintype.card (L → G) * Fintype.card G ^
        (Fintype.card L - Fintype.card (arrangementGraph m e).ConnectedComponent) := by
  choose pivot hpivot using arrangementRight_surjective hm e
  rw [Fintype.card_congr (arrangementRangeEquiv (G := G) hm e)]
  exact (Fintype.card_subtype _).trans (card_pairedPartitions
    (arrangementLeft e) (arrangementRight e) (fun c => ⟨pivot c, hpivot c⟩))

theorem pairedPartitionCorrelation_fintype {L C G : Type*} [Finite L] [Finite C] [Finite G]
    [CommGroup G] (fL : Fintype L) (fC : Fintype C) (fG : Fintype G)
    (dL : DecidableEq L) (dC : DecidableEq C) (dG : DecidableEq G)
    (a b : L → C) (F H : (L → G) → ℂ) :
    @pairedPartitionCorrelation L C G fL fC dL dC _ fG dG a b F H =
      @pairedPartitionCorrelation L C G (Fintype.ofFinite L) (Fintype.ofFinite C)
        (Classical.decEq L) (Classical.decEq C) _ (Fintype.ofFinite G) (Classical.decEq G) a b F H := by
  cases Subsingleton.elim fL (Fintype.ofFinite L)
  cases Subsingleton.elim fC (Fintype.ofFinite C)
  cases Subsingleton.elim fG (Fintype.ofFinite G)
  cases Subsingleton.elim dL (Classical.decEq L)
  cases Subsingleton.elim dC (Classical.decEq C)
  cases Subsingleton.elim dG (Classical.decEq G)
  rfl

theorem arrangement_uniform_correlation {L G : Type*} [Fintype L] [CommGroup G]
    [Fintype G] {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m))
    (F H : (L → G) → ℂ) :
    (Fintype.card (L × Fin m → G) : ℂ)⁻¹ *
      (∑ x : L × Fin m → G, F (bulkBlockProduct x) * conj (H (bulkBlockProduct (x ∘ e.symm)))) =
      pairedPartitionCorrelation (arrangementLeft e) (arrangementRight e) F H := by
  have hu := uniform_hom_average (arrangementProductMap (G := G) e).rangeRestrict
    (arrangementProductMap (G := G) e).rangeRestrict_surjective
    (fun y => F y.val.1 * conj (H y.val.2))
  change _ = (Fintype.card (arrangementProductMap (G := G) e).range : ℂ)⁻¹ * _ at hu
  rw [arrangementProductMap_range_card hm e] at hu
  apply hu.trans
  unfold pairedPartitionCorrelation
  push_cast
  congr 1
  rw [← (arrangementRangeEquiv (G := G) hm e).symm.sum_comp
    (fun y => F y.val.1 * conj (H y.val.2))]
  change (∑ y : {ab : (L → G) × (L → G) //
    partitionProduct (arrangementLeft e) ab.1 = partitionProduct (arrangementRight e) ab.2},
    F y.val.1 * conj (H y.val.2)) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun ab : (L → G) × (L → G) =>
    partitionProduct (arrangementLeft e) ab.1 = partitionProduct (arrangementRight e) ab.2))
    (by simp) (fun ab => F ab.1 * conj (H ab.2))]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem arrangement_uniform_norm_sq_le {L G : Type*} [Fintype L] [CommGroup G]
    [Fintype G] {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m))
    (F H : (L → G) → ℂ) (B : ℝ)
    (h : ‖pairedPartitionCorrelation (arrangementLeft e) (arrangementRight e) F H‖ ^ 2 ≤ B) :
    ‖bulkPairCorrelation e F H‖ ^ 2 ≤ B := by
  unfold bulkPairCorrelation
  rw [arrangement_uniform_correlation hm e F H]
  exact h

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
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ArrangementTreeComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the quartet comparison to actual overlap components -/

namespace Ostmann

open scoped BigOperators Classical

theorem arrangement_tree_component_count {n m : ℕ}
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2))) :
    Fintype.card (arrangementGraph m e).ConnectedComponent ≤ 3 * 2 ^ n := by
  rw [card_treeLeafIndex, pow_add] at hgood
  norm_num at hgood
  omega

/-- All component maps and their nonempty fibers are obtained from the
actual bulk permutation; only the local Fourier bound is supplied. -/
theorem arrangement_tree_comparison {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (D₁ D₂ : (ZMod p)ˣ) {K₁ K₂ : (ZMod p)ˣ}
    (T₁ : RationalTreeData (ZMod p)ˣ (n + 2) K₁)
    (T₂ : RationalTreeData (ZMod p)ˣ (n + 2) K₂)
    (XL₁ XR₁ XL₂ XR₂ : (ZMod p)ˣ) (c₁ c₂ : TreeLeafTuple Bool (n + 2))
    (cL cR : TreeLeafIndex n → Bool)
    (hconj : ∀ q, quartetBlockEquiv Bool n c₁ q = ((cL q, !(cL q)), (cR q, !(cR q)))) :
    ‖pairedPartitionCorrelation (arrangementLeft e) (arrangementRight e)
      (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁)
      (indexedRationalAmplitude g D₂ T₂ XL₂ XR₂ c₂)‖ ^ 2 ≤
      (3 : ℝ) ^ (2 ^ (n + 2)) * ((2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1))) := by
  choose pivot₁ hpivot₁ using arrangementLeft_surjective hm e
  choose pivot₂ hpivot₂ using arrangementRight_surjective hm e
  exact pairedRationalTree_comparison hp g hg henergy ε hε hflat n
    (arrangementLeft e) (arrangementRight e)
    (fun c => ⟨pivot₁ c, hpivot₁ c⟩) (fun c => ⟨pivot₂ c, hpivot₂ c⟩)
    (arrangement_tree_component_count e hgood)
    D₁ D₂ T₁ T₂ XL₁ XR₁ XL₂ XR₂ c₁ c₂ cL cR hconj

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ArrangementBulkComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quartet estimate for the original independent bulk-slot residues -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem arrangement_tree_bulk_comparison {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (D₁ D₂ : (ZMod p)ˣ) {K₁ K₂ : (ZMod p)ˣ}
    (T₁ : RationalTreeData (ZMod p)ˣ (n + 2) K₁)
    (T₂ : RationalTreeData (ZMod p)ˣ (n + 2) K₂)
    (XL₁ XR₁ XL₂ XR₂ : (ZMod p)ˣ) (c₁ c₂ : TreeLeafTuple Bool (n + 2))
    (cL cR : TreeLeafIndex n → Bool)
    (hconj : ∀ q, quartetBlockEquiv Bool n c₁ q = ((cL q, !(cL q)), (cR q, !(cR q)))) :
    ‖bulkPairCorrelation e
      (indexedRationalAmplitude g D₁ T₁ XL₁ XR₁ c₁)
      (indexedRationalAmplitude g D₂ T₂ XL₂ XR₂ c₂)‖ ^ 2 ≤
      (3 : ℝ) ^ (2 ^ (n + 2)) * ((2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1))) := by
  apply arrangement_uniform_norm_sq_le hm e
  simpa only [pairedPartitionCorrelation_fintype] using
    (arrangement_tree_comparison hp g hg henergy ε hε hflat n m hm e hgood
      D₁ D₂ T₁ T₂ XL₁ XR₁ XL₂ XR₂ c₁ c₂ cL cR hconj)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorBulkComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform signed comparison at all spectator primes -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem spectator_bulk_comparison {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (g : ZMod p → ℂ) (hg : g 0 = 0) (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hflat : MixedFourierBound g ε)
    (d₁ d₂ : SpectatorDiagram p (n + 2)) (cL cR : TreeLeafIndex n → Bool)
    (hconj : ∀ q, quartetBlockEquiv Bool n d₁.conjugations q =
      ((cL q, !(cL q)), (cR q, !(cR q)))) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ) : ℂ)⁻¹ *
      (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ,
        d₁.bulkValue g x * conj (d₂.bulkValue g (x ∘ e.symm)))‖ ^ 2 ≤
      quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) := by
  have h := (arrangement_tree_bulk_comparison hp g hg henergy ε hε hflat n m hm e hgood
    d₁.D d₂.D d₁.tree d₂.tree d₁.XL d₁.XR d₂.XL d₂.XR d₁.conjugations d₂.conjugations
    cL cR hconj).trans (quartetTree_error_le hp n ε hε hε1)
  simpa only [bulkPairCorrelation, SpectatorDiagram.bulkValue, finite_univ_canonical,
    Fintype.card_eq_nat_card] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferConjugations
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual transfer has opposite conjugations in every bottom sibling pair -/

namespace Ostmann

theorem transferConjugations_quartet (n : ℕ) (b : Bool) (q : TreeLeafIndex n) :
    quartetBlockEquiv Bool n (transferConjugations (n + 2) b) q =
      let c := treeLeafTupleEquiv Bool n (transferConjugations n b) q
      ((c, !c), (!c, c)) := by
  induction n generalizing b with
  | zero => cases q; cases b <;> rfl
  | succ n ih =>
    cases q with
    | inl q => exact ih b q
    | inr q => exact ih (!b) q

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantSamples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the moving-giant tree from the sampled compensation slots

Each reversing node samples four positions per leaf of either child. Their
products are inserted into both child regular lists. The constructor proves
the required product consistency; it does not ask for a pre-existing diagram.
-/

namespace Ostmann
open scoped BigOperators

/-- Unit conditions for the diagram follow from the actual sampled products
and original frequency bounds. They are independent of the bulk variables. -/
theorem buildMovingGiantTree_units {q n : ℕ} [Fact q.Prime] (t : FrequencyTree ℤ n)
    (small : TreeLeafTuple ℕ n) (samples : MovingGiantSamples n)
    (hfreq : movingGiantFrequencyUnits q n t)
    (hsmall : ((treeLeafProduct n small : ℕ) : ZMod q) ≠ 0)
    (hsamples : samples.UnitsAt q) :
    (buildMovingGiantTree n t small samples).UnitsAt q := by
  induction samples with
  | leaf => exact ⟨hfreq, hsmall⟩
  | @node n samples left right ihL ihR =>
    have hparts : ((treeLeafProduct n small.1 : ℕ) : ZMod q) ≠ 0 ∧
        ((treeLeafProduct n small.2 : ℕ) : ZMod q) ≠ 0 := by
      simpa only [treeLeafProduct, Nat.cast_mul, mul_ne_zero_iff] using hsmall
    refine ⟨hfreq.1, hparts.1, hparts.2, hsamples.1, ?_, ?_⟩
    · rw [MovingGiantTree.castConstant_units]
      apply ihL _ _ hfreq.2.1 _ hsamples.2.1
      rw [multiplySmallLeaves_product, Nat.cast_mul]
      exact mul_ne_zero hsamples.1 hparts.1
    · rw [MovingGiantTree.castConstant_units]
      apply ihR _ _ hfreq.2.2 _ hsamples.2.2
      rw [multiplySmallLeaves_product, Nat.cast_mul]
      exact mul_ne_zero hsamples.1 hparts.2

theorem movingGiantFrequencyUnits_of_bounds {q n : ℕ} [Fact q.Prime]
    (t : FrequencyTree ℤ n)
    (h : ∀ s ∈ allFrequencyList n t, s ≠ 0 ∧ s.natAbs < q) :
    movingGiantFrequencyUnits q n t := by
  induction n with
  | zero =>
    have hs := h (frequencyRoot 0 t) (by simp [allFrequencyList, frequencyRoot])
    exact spectator_frequency_ne_zero _ hs.1 hs.2
  | succ n ih =>
    refine ⟨spectator_frequency_ne_zero _ (h t.1 (by simp [allFrequencyList])).1
      (h t.1 (by simp [allFrequencyList])).2, ?_, ?_⟩
    · apply ih t.2.1
      intro s hs
      exact h s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))
    · apply ih t.2.2
      intro s hs
      exact h s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleValues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

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

theorem movingCompensationValues_product {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x : TreeLeafTuple (Fin 4 → σ) n) :
    movingSlotValues value n (movingCompensationSlots n x) =
      compensationLeafProducts n (movingCompensationValues value n x) := by
  induction n with
  | zero =>
    change ((List.ofFn (show Fin 4 → σ from x)).map value).prod = ∏ i : Fin 4, value (x i)
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

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
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

/-- On the balanced supports used in the construction, the physical function
has a fixed pointwise bound. -/
theorem normalizedResidueIndicator_norm_le_three {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (x : ZMod p) :
    ‖normalizedResidueIndicator S x‖ ≤ 3 := by
  have hv : (1 / 9 : ℝ) ≤ residueVariance S := by
    dsimp [residueVariance]
    nlinarith
  have hs : (1 / 3 : ℝ) ≤ Real.sqrt (residueVariance S) := by
    have hh := Real.sq_sqrt (show 0 ≤ residueVariance S by linarith)
    nlinarith [Real.sqrt_nonneg (residueVariance S)]
  have hsp : 0 < Real.sqrt (residueVariance S) := by linarith
  simp only [normalizedResidueIndicator, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos hsp]
  apply (div_le_iff₀ hsp).mpr
  have hb := centeredDensity_abs_le S x
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedMixedFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixed Fourier coefficients of the normalized residue transform

The principal coefficient is controlled by Fourier inversion. Nonprincipal
coefficients are exactly the translated residue bias times its density factor.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem additiveFourier_densityFourier {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (densityFourier f) a =
      (Real.sqrt (p : ℝ) : ℂ) * (p : ℂ)⁻¹ * f (-a) := by
  change additiveFourier (fun x => (Real.sqrt (p : ℝ) : ℂ) * additiveFourier f x) a = _
  rw [additiveFourier_const_mul, additiveFourier_twice]
  ring

theorem normalizedResidueTransform_principal {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (a : ZMod p) :
    ‖additiveFourier (fun x => normalizedResidueTransform S x * (1 : MulChar (ZMod p) ℂ) x) a‖ =
      ‖normalizedResidueIndicator S (-a)‖ / Real.sqrt (p : ℝ) := by
  have he : (fun x => normalizedResidueTransform S x * (1 : MulChar (ZMod p) ℂ) x) =
      normalizedResidueTransform S := by
    funext x
    by_cases hx : x = 0
    · simp [hx, normalizedResidueTransform_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx), mul_one]
  rw [he, normalizedResidueTransform, additiveFourier_densityFourier,
    norm_mul, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  have hs2 := Real.sq_sqrt hp.le
  field_simp
  rw [hs2]

theorem densityFourier_mixed_character {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    additiveFourier (fun x => densityFourier f x * χ x) a =
      ((Real.sqrt (p : ℝ) : ℂ) * (p : ℂ)⁻¹ ^ 2 * gaussSum χ ZMod.stdAddChar) *
        ∑ x : ZMod p, f x * χ⁻¹ (-a - x) := by
  rw [additiveFourier_mul_character _ χ hχ]
  simp_rw [additiveFourier_densityFourier]
  have he : (∑ b : ZMod p, f (-b) * χ⁻¹ (-(a - b))) =
      ∑ x : ZMod p, f x * χ⁻¹ (-a - x) := by
    have hh := (Equiv.neg (ZMod p)).bijective.sum_comp (fun x => f x * χ⁻¹ (-a - x))
    simpa only [Equiv.neg_apply, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm] using hh
  calc
    _ = ((Real.sqrt (p : ℝ) : ℂ) * (p : ℂ)⁻¹ ^ 2 * gaussSum χ ZMod.stdAddChar) *
        ∑ b : ZMod p, f (-b) * χ⁻¹ (-(a - b)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [he]

theorem normalizedResidueIndicator_character_sum {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    (∑ x : ZMod p, normalizedResidueIndicator S x * χ⁻¹ (-a - x)) =
      (Real.sqrt (residueVariance S) : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x) := by
  have hsum : (∑ x : ZMod p, χ⁻¹ (-a - x)) = 0 := by
    have hh := (Equiv.subLeft (-a)).bijective.sum_comp (fun x => χ⁻¹ x)
    change (∑ x : ZMod p, χ⁻¹ (-a - x)) = ∑ x : ZMod p, χ⁻¹ x at hh
    rw [hh]
    exact MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hχ)
  have hf (x : ZMod p) : normalizedResidueIndicator S x =
      (Real.sqrt (residueVariance S) : ℂ)⁻¹ *
        ((if x ∈ S then 1 else 0) - (residueDensity S : ℂ)) := by
    simp only [normalizedResidueIndicator, centeredDensity, residueDensity,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast]
    split <;> push_cast <;> ring
  simp_rw [hf, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  simp

theorem normalizedResidueTransform_nonprincipal {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p)
    (hS : S.Nonempty) (hSp : S.card < p) :
    ‖additiveFourier (fun x => normalizedResidueTransform S x * χ x) a‖ =
      residueDensity S / Real.sqrt (residueVariance S) *
        ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ := by
  rw [normalizedResidueTransform, densityFourier_mixed_character _ χ hχ,
    normalizedResidueIndicator_character_sum S χ hχ a]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hv := residueVariance_pos S hS hSp
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  have hsv : 0 < Real.sqrt (residueVariance S) := Real.sqrt_pos.mpr hv
  have hgauss : ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ = Real.sqrt (p : ℝ) := by
    have hh := gaussSum_norm_sq χ hχ
    have he := Real.sq_sqrt hp.le
    nlinarith [norm_nonneg (gaussSum χ (ZMod.stdAddChar (N := p))), Real.sqrt_nonneg (p : ℝ)]
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs, abs_of_pos hsv, hgauss, residueDensity]
  have hs2 := Real.sq_sqrt hp.le
  field_simp
  rw [hs2]

/-- The exact Gauss identity supplies the local mixed bound used by the tree
comparison once the translated character means have been bounded. -/
theorem normalizedResidueTransform_mixedBound {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (β : ℝ)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β) :
    MixedFourierBound (normalizedResidueTransform S)
      (max (3 / Real.sqrt (p : ℝ)) (2 * β)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < S.card := by
      have hh : 0 < residueDensity S := by linarith
      exact (div_pos_iff_of_pos_right hp).mp hh
    exact_mod_cast hpos
  have hSp : S.card < p := by
    have hh : residueDensity S < 1 := by linarith
    exact_mod_cast (div_lt_one hp).mp hh
  have hv : (1 / 9 : ℝ) ≤ residueVariance S := by
    dsimp [residueVariance]
    nlinarith
  have hs : (1 / 3 : ℝ) ≤ Real.sqrt (residueVariance S) := by
    have hh := Real.sq_sqrt (show 0 ≤ residueVariance S by linarith)
    nlinarith [Real.sqrt_nonneg (residueVariance S)]
  have hsv : 0 < Real.sqrt (residueVariance S) := by linarith
  have hratio : residueDensity S / Real.sqrt (residueVariance S) ≤ 2 :=
    (div_le_iff₀ hsv).mpr (by linarith)
  intro χ a
  by_cases hχ : χ = 1
  · subst χ
    rw [normalizedResidueTransform_principal]
    exact (div_le_div_of_nonneg_right (normalizedResidueIndicator_norm_le_three S hlo hhi (-a))
      (Real.sqrt_nonneg _)).trans (le_max_left _ _)
  · rw [normalizedResidueTransform_nonprincipal S χ hχ a hS hSp]
    exact (mul_le_mul hratio (hbias χ hχ a) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans
      (le_max_right _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_NormalizedSpectatorComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the bulk comparison to the actual balanced residue supports -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem normalizedResidueTransform_mixed_le {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (β ε : ℝ)
    (hprincipal : 3 / Real.sqrt (p : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β) :
    MixedFourierBound (normalizedResidueTransform S) ε := by
  have h := normalizedResidueTransform_mixedBound S hlo hhi β hbias
  intro χ a
  exact (h χ a).trans (max_le hprincipal hβ)

theorem normalized_spectator_bulk_comparison {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSp : S.card < p)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (p : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (d₁ d₂ : SpectatorDiagram p (n + 2)) (cL cR : TreeLeafIndex n → Bool)
    (hconj : ∀ q, quartetBlockEquiv Bool n d₁.conjugations q =
      ((cL q, !(cL q)), (cR q, !(cR q)))) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ) : ℂ)⁻¹ *
      (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ,
        d₁.bulkValue (normalizedResidueTransform S) x *
          conj (d₂.bulkValue (normalizedResidueTransform S) (x ∘ e.symm)))‖ ^ 2 ≤
      quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) := by
  exact spectator_bulk_comparison hp n m hm e hgood (normalizedResidueTransform S)
    (normalizedResidueTransform_zero S) (normalizedResidueTransform_energy S hS hSp).le
    ε hε hε1 (normalizedResidueTransform_mixed_le S hlo hhi β ε hprincipal hβ hbias)
    d₁ d₂ cL cR hconj

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSpectatorPageBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual normalized spectator gain used in the bulk Page average -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The numerical quartet estimate gives the local hypothesis of
`bulk_residue_page_bound`, for the actual balanced residue transform. -/
theorem normalized_bulk_spectator_mean_le {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSp : S.card < p)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (p : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (d₁ d₂ : SpectatorDiagram p (n + 2)) (cL cR : TreeLeafIndex n → Bool)
    (hconj : ∀ j, quartetBlockEquiv Bool n d₁.conjugations j =
      ((cL j, !(cL j)), (cR j, !(cR j))))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) ≤ δ ^ 2) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ) : ℂ)⁻¹ *
      (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ,
        d₁.bulkValue (normalizedResidueTransform S) x *
          conj (d₂.bulkValue (normalizedResidueTransform S) (x ∘ e.symm)))‖ ≤ δ := by
  apply (sq_le_sq₀ (norm_nonneg _) hδ).mp
  exact (normalized_spectator_bulk_comparison hp n m hm e hgood S hlo hhi hS hSp
    β ε hε hε1 hprincipal hβ hbias d₁ d₂ cL cR hconj).trans hnum

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFieldGiant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual moving-giant recursion directly over the spectator field -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- This is a field identity on all bulk residues, so the later averaging
does not require an integer lift satisfying the original division tests. -/
theorem MovingGiantTree.exists_field_diagram {q : ℕ} [Fact q.Prime]
    {n C : ℕ} (T : MovingGiantTree n C) (hT : T.UnitsAt q) :
    ∃ (U : (ZMod q)ˣ) (R : RationalTreeData (ZMod q)ˣ n U),
      (C : ZMod q) = U ∧ (T.frequency : ZMod q) = R.frequency ∧
      ∀ (g : ZMod q → ℂ) (D A B : (ZMod q)ˣ)
        (z : TreeLeafTuple (ZMod q)ˣ n) (b : Bool),
        (if b then conj (movingFieldGiantAmplitude g D T A B z)
          else movingFieldGiantAmplitude g D T A B z) =
          rationalTreeAmplitude g D R A B (transferConjugations n b) z := by
  induction T with
  | leaf s C =>
    let S : (ZMod q)ˣ := Units.mk0 (s : ZMod q) hT.1
    let U : (ZMod q)ˣ := Units.mk0 (C : ZMod q) hT.2
    refine ⟨U, .leaf S U, rfl, rfl, ?_⟩
    intro g D A B z b
    have he : (s : ZMod q) / ((D : ZMod q) * A * B * C * (show (ZMod q)ˣ from z)) =
        (rationalTreeArgument S U D A B z : ZMod q) := by
      simp only [rationalTreeArgument, Units.val_div_eq_div_val, Units.val_mul,
        S, U, Units.val_mk0]
    cases b <;> simp only [movingFieldGiantAmplitude, he, rationalTreeAmplitude,
      transferConjugations, Bool.false_eq_true, ↓reduceIte, Complex.star_def]
  | @node n s CL CR u left right ihL ihR =>
    obtain ⟨hs, hCL, hCR, hu, hl, hr⟩ := hT
    let S : (ZMod q)ˣ := Units.mk0 (s : ZMod q) hs
    let A₀ : (ZMod q)ˣ := Units.mk0 (CL : ZMod q) hCL
    let B₀ : (ZMod q)ˣ := Units.mk0 (CR : ZMod q) hCR
    let U₀ : (ZMod q)ˣ := Units.mk0 (u : ZMod q) hu
    obtain ⟨UL, L, hUL, hfL, hL⟩ := ihL hl
    obtain ⟨UR, R, hUR, hfR, hR⟩ := ihR hr
    have eL : UL = U₀ * A₀ := by
      apply Units.ext
      simpa only [U₀, A₀, Units.val_mul, Units.val_mk0, Nat.cast_mul] using hUL.symm
    have eR : UR = U₀ * B₀ := by
      apply Units.ext
      simpa only [U₀, B₀, Units.val_mul, Units.val_mk0, Nat.cast_mul] using hUR.symm
    subst UL
    subst UR
    refine ⟨A₀ * B₀, .node S A₀ B₀ U₀ L R, ?_, rfl, ?_⟩
    · simp only [Nat.cast_mul, Units.val_mul, Units.val_mk0, A₀, B₀]
    intro g D A B z b
    let v := reconstructedEntry (s : ZMod q) (left.frequency : ZMod q)
      (right.frequency : ZMod q) (u : ZMod q)
      ((A : ZMod q) * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
      ((B : ZMod q) * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ))
    have hrec : reconstructedEntry (S : ZMod q) L.frequency R.frequency U₀
        ((A * A₀ * treeLeafProduct n z.1 : (ZMod q)ˣ) : ZMod q)
        ((B * B₀ * treeLeafProduct n z.2 : (ZMod q)ˣ) : ZMod q) = v := by
      simp only [v, hfL, hfR, S, U₀, A₀, B₀, Units.val_mul, Units.val_mk0]
    by_cases hv : v = 0
    · cases b <;> simp only [movingFieldGiantAmplitude, show
        reconstructedEntry (s : ZMod q) (left.frequency : ZMod q) (right.frequency : ZMod q)
          (u : ZMod q) ((A : ZMod q) * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
          ((B : ZMod q) * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ)) = 0 from hv,
        ↓reduceIte, map_zero, rationalTreeAmplitude, hrec, hv, Bool.false_eq_true, dite_true]
    · let V : (ZMod q)ˣ := Units.mk0 v hv
      have hleft := hL g D V A z.1 b
      have hright := hR g D V B z.2 (!b)
      have hV : Units.mk0
          (reconstructedEntry (S : ZMod q) L.frequency R.frequency U₀
            ((A * A₀ * treeLeafProduct n z.1 : (ZMod q)ˣ) : ZMod q)
            ((B * B₀ * treeLeafProduct n z.2 : (ZMod q)ˣ) : ZMod q))
          (by rw [hrec]; exact hv) = V := Units.ext hrec
      simp only [movingFieldGiantAmplitude, show
        reconstructedEntry (s : ZMod q) (left.frequency : ZMod q) (right.frequency : ZMod q)
          (u : ZMod q) ((A : ZMod q) * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
          ((B : ZMod q) * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ)) ≠ 0 from hv,
        ↓reduceIte, rationalTreeAmplitude, transferConjugations]
      rw [dite_eq_right (by rw [hrec]; exact hv), hV, ← hleft, ← hright]
      cases b <;> simp [V, v]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBulkPageBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the actual transfer conjugations with the bulk Page density -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The conjugations proved for the original moving slot diagrams give the
required quartet conjugations without any further combinatorial hypothesis. -/
theorem normalized_transfer_bulk_mean {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSp : S.card < p)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (p : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (d₁ d₂ : SpectatorDiagram p (n + 2))
    (hd : d₁.conjugations = transferConjugations (n + 2) false)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) ≤ δ ^ 2) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ) : ℂ)⁻¹ *
      ∑ z, d₁.bulkValue (normalizedResidueTransform S) z *
        conj (d₂.bulkValue (normalizedResidueTransform S) (z ∘ e.symm))‖ ≤ δ := by
  let c := treeLeafTupleEquiv Bool n (transferConjugations n false)
  have hconj (j : TreeLeafIndex n) :
      quartetBlockEquiv Bool n d₁.conjugations j =
        ((c j, !(c j)), ((!(c j)), !(!(c j)))) := by
    rw [hd]
    simpa only [Bool.not_not] using transferConjugations_quartet n false j
  exact normalized_bulk_spectator_mean_le hp n m hm e hgood S hlo hhi hS hSp
    β ε hε hε1 hprincipal hβ hbias d₁ d₂ c (fun j => !(c j)) hconj δ hδ hnum

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSpectatorAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual spectator Haar factor as a fixed function of the bulk residues -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

private theorem norm_finite_average_le {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℂ) (δ : ℝ) (hf : ∀ a, ‖f a‖ ≤ δ) :
    ‖(Fintype.card A : ℂ)⁻¹ * ∑ a, f a‖ ≤ δ := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _a : A, δ :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hf a))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = δ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem frozenBulkSpectatorPair_mean_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (hq : 3 ≤ q) (base : σ → ℕ) (n m : ℕ) (hm : 0 < m)
    (t : Bool → FrequencyTree ℤ (n + 2))
    (small : Bool → TreeLeafTuple (List σ) (n + 2))
    (samples : Bool → MovingSampleSlots σ (n + 2))
    (hfreq : ∀ b, movingGiantFrequencyUnits q (n + 2) (t b))
    (hsmall : ∀ b, ((treeLeafProduct (n + 2) (movingSlotValues base (n + 2) (small b)) : ℕ) :
      ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (S : Finset (ZMod q)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSq : S.card < q)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (q : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod q) ℂ), χ ≠ 1 → ∀ a : ZMod q,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (q : ℝ))) ≤ δ ^ 2)
    (a : (ZMod q)ˣ × (ZMod q)ˣ) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
      ∑ z, frozenBulkSpectatorPair base (n + 2) m t small samples D e
        (normalizedResidueTransform S) a z‖ ≤ δ := by
  have hex (b : Bool) := (buildMovingGiantTree (n + 2) (t b)
    (movingSlotValues base (n + 2) (small b)) ((samples b).values base)).exists_field_diagram
      (buildMovingGiantTree_units (t b) _ _ (hfreq b) (hsmall b) (hsamples b))
  choose U R _ _ hR using hex
  let d (b : Bool) : SpectatorDiagram q (n + 2) :=
    ⟨D b, U b, R b, a.1, a.2, transferConjugations (n + 2) false⟩
  have he (z : TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) :
      frozenBulkSpectatorPair base (n + 2) m t small samples D e
        (normalizedResidueTransform S) a z =
      (d false).bulkValue (normalizedResidueTransform S) z *
        conj ((d true).bulkValue (normalizedResidueTransform S) (z ∘ e.symm)) := by
    unfold frozenBulkSpectatorPair
    rw [show movingFieldGiantAmplitude (normalizedResidueTransform S) (D false)
        (buildMovingGiantTree (n + 2) (t false) (movingSlotValues base (n + 2) (small false))
          ((samples false).values base)) a.1 a.2 _ = _ from
        hR false (normalizedResidueTransform S) (D false) a.1 a.2 _ false,
      show movingFieldGiantAmplitude (normalizedResidueTransform S) (D true)
        (buildMovingGiantTree (n + 2) (t true) (movingSlotValues base (n + 2) (small true))
          ((samples true).values base)) a.1 a.2 _ = _ from
        hR true (normalizedResidueTransform S) (D true) a.1 a.2 _ false]
    rfl
  simp_rw [he]
  exact normalized_transfer_bulk_mean hq n m hm e hgood S hlo hhi hS hSq
    β ε hε hε1 hprincipal hβ hbias (d false) (d true) rfl δ hδ hnum

theorem frozenBulkSpectatorHaar_mean_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (hq : 3 ≤ q) (base : σ → ℕ) (n m : ℕ) (hm : 0 < m)
    (t : Bool → FrequencyTree ℤ (n + 2))
    (small : Bool → TreeLeafTuple (List σ) (n + 2))
    (samples : Bool → MovingSampleSlots σ (n + 2))
    (hfreq : ∀ b, movingGiantFrequencyUnits q (n + 2) (t b))
    (hsmall : ∀ b, ((treeLeafProduct (n + 2) (movingSlotValues base (n + 2) (small b)) : ℕ) :
      ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (S : Finset (ZMod q)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSq : S.card < q)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (q : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod q) ℂ), χ ≠ 1 → ∀ a : ZMod q,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (q : ℝ))) ≤ δ ^ 2)
    : ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
      ∑ z, frozenBulkSpectatorHaar base (n + 2) m t small samples D e
        (normalizedResidueTransform S) z‖ ≤ δ := by
  let F := frozenBulkSpectatorPair base (n + 2) m t small samples D e
    (normalizedResidueTransform S)
  have hpair (a : (ZMod q)ˣ × (ZMod q)ˣ) :
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
        ∑ z, F a z‖ ≤ δ :=
    frozenBulkSpectatorPair_mean_le hq base n m hm t small samples hfreq hsmall
      hsamples D e hgood S hlo hhi hS hSq β ε hε hε1 hprincipal hβ hbias δ hδ hnum a
  have hmean := norm_finite_average_le _ δ hpair
  have hswap :
      (Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
        ∑ z, frozenBulkSpectatorHaar base (n + 2) m t small samples D e
          (normalizedResidueTransform S) z =
      ((Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)) *
        ((Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ) : ℂ)⁻¹ *
          ∑ a, (Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
            ∑ z, F a z) := by
    simp only [frozenBulkSpectatorHaar, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro z _
    dsimp only [F]
    ring
  have hratio : ‖(Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_one (by positivity : (0 : ℝ) < q)).mpr
    exact_mod_cast (ZMod.card_units q ▸ Nat.sub_le q 1)
  rw [hswap, norm_mul]
  exact (mul_le_mul_of_nonneg_left hmean (norm_nonneg _)).trans
    (by simpa using mul_le_mul_of_nonneg_right hratio hδ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SignedBulkGain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the quartet gain after the actual bulk-slot counting loss -/

namespace Ostmann
open scoped Classical BigOperators

theorem signedBulkGainTarget_pos (n : ℕ) (C D : ℝ) : 0 < signedBulkGainTarget n C D :=
  Real.exp_pos _

theorem signedBulkGainTarget_absorbs (n m : ℕ) (C D : ℝ) :
    Real.exp (C * m) * 4 ^ (2 ^ n * m) * (signedBulkGainTarget n C D) ^ m =
      Real.exp (-D * m) := by
  have hfour : (4 : ℝ) ^ (2 ^ n * m) = Real.exp ((2 ^ n * m : ℕ) * Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [hfour, signedBulkGainTarget, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The actual number of bulk positions is `2^n*m`, while the gain is
multiplied once for each of the `m` spectator primes. -/
theorem signedBulkGainTarget_bound (n m : ℕ) (C D W A δ : ℝ)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hamp : A ≤ Real.exp (C * m)) (hgain : δ ≤ signedBulkGainTarget n C D) :
    (W * A) * 4 ^ Fintype.card (TreeLeafIndex n × Fin m) * δ ^ m ≤
      W * Real.exp (-D * m) := by
  rw [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin]
  calc
    _ ≤ (W * A) * 4 ^ (2 ^ n * m) * (signedBulkGainTarget n C D) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ hgain m)
        (mul_nonneg (mul_nonneg hW hA) (by positivity))
    _ ≤ (W * Real.exp (C * m)) * 4 ^ (2 ^ n * m) * (signedBulkGainTarget n C D) ^ m :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hamp hW) (by positivity))
        (pow_nonneg (signedBulkGainTarget_pos n C D).le m)
    _ = _ := by rw [mul_assoc W, mul_assoc W, signedBulkGainTarget_absorbs]

/-- One fixed mixed-Fourier tolerance and one prime threshold give the gain
needed for any requested exponential rate, uniformly in the bulk length. -/
theorem exists_signedBulkGain_parameters (n : ℕ) (C D : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ p : ℕ, N ≤ p →
        3 / Real.sqrt (p : ℝ) ≤ ε ∧
        quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) ≤
          (signedBulkGainTarget (n + 2) C D) ^ 2 := by
  obtain ⟨ε, hε, hε1, N, hN, hnum⟩ := exists_quartet_small_parameters
    (quartetTreeConstant n) (signedBulkGainTarget (n + 2) C D)
    (quartetTreeConstant_pos n) (signedBulkGainTarget_pos _ _ _)
  refine ⟨ε, hε, hε1, max N ⌈(3 / ε) ^ 2⌉₊, hN.trans (le_max_left _ _), ?_⟩
  intro p hp
  have hpN : N ≤ p := (le_max_left _ _).trans hp
  refine ⟨?_, hnum p hpN⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < N) hpN)
  have hbound : (3 / ε) ^ 2 ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hp))
  have hsqrt : 3 / ε ≤ Real.sqrt (p : ℝ) :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr hbound
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hp0)).mpr
  have h := (div_le_iff₀ hε).mp hsqrt
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenSpectatorGain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.movingSampleSlotsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

/-- The tolerance and threshold depend only on the fixed depth and the
requested exponential saving. All base values, sample trees, matchings and
bulk lengths remain variable. -/
theorem exists_frozenSpectatorGain (n : ℕ) (C D : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ (q : ℕ) [Fact q.Prime], N ≤ q →
      ∀ (σ : Type*) (base : σ → ℕ) (m : ℕ), 0 < m →
      ∀ (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List σ) (n + 2))
        (samples : Bool → MovingSampleSlots σ (n + 2)),
      (∀ b, movingGiantFrequencyUnits q (n + 2) (t b)) →
      (∀ b, ((treeLeafProduct (n + 2) (movingSlotValues base (n + 2) (small b)) : ℕ) :
        ZMod q) ≠ 0) →
      (∀ b, ((samples b).values base).UnitsAt q) →
      ∀ (twist : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m)),
      4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      ∀ (S : Finset (ZMod q)), (1 / 3 : ℝ) ≤ residueDensity S →
      residueDensity S ≤ 2 / 3 → S.Nonempty → S.card < q →
      ∀ β : ℝ, 2 * β ≤ ε →
      (∀ (χ : MulChar (ZMod q) ℂ), χ ≠ 1 → ∀ a : ZMod q,
        ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β) →
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
        ∑ z, frozenBulkSpectatorHaar base (n + 2) m t small samples twist e
          (normalizedResidueTransform S) z‖ ≤ signedBulkGainTarget (n + 2) C D := by
  obtain ⟨ε, hε, hε1, N, hN, hnum⟩ := exists_signedBulkGain_parameters n C D
  refine ⟨ε, hε, hε1, N, hN, ?_⟩
  intro q hq hqN σ base m hm t small samples hfreq hsmall hsamples twist e hgood S hlo hhi hS hSq β hβ hbias
  exact frozenBulkSpectatorHaar_mean_le (hN.trans hqN) base n m hm t small samples
    hfreq hsmall hsamples twist e hgood S hlo hhi hS hSq β ε hε.le hε1
    (hnum q hqN).1 hβ hbias (signedBulkGainTarget (n + 2) C D)
    (signedBulkGainTarget_pos _ _ _).le (hnum q hqN).2

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
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternSpectatorUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The spectator unit conditions from the actual pattern coordinates -/

namespace Ostmann
open scoped Classical

theorem movingSlotValues_unit {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (n : ℕ) (small : TreeLeafTuple (List σ) n)
    (h : ∀ i ∈ flattenMovingSlots n small, (value i : ZMod q) ≠ 0) :
    ((treeLeafProduct n (movingSlotValues value n small) : ℕ) : ZMod q) ≠ 0 := by
  rw [← movingSlotValues_flatten, MovingSlotReversal.naturalProduct, Nat.cast_list_prod, List.map_map]
  apply List.prod_ne_zero
  intro hz
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hz
  exact h i hi he

theorem MovingSampleSlots.values_units_of_coordinates {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) {n : ℕ} (samples : MovingSampleSlots σ n)
    (h : ∀ i, (value (movingSampleCoordinates σ n samples i) : ZMod q) ≠ 0) :
    (samples.values value).UnitsAt q := by
  induction samples with
  | leaf => trivial
  | @node n u l r ihL ihR =>
    refine ⟨?_, ihL (fun i => h (.inr (true, i))), ihR (fun i => h (.inr (false, i)))⟩
    rw [← movingCompensationValues_product]
    apply movingSlotValues_unit
    apply movingCompensationSlots_forall
    intro a j
    exact h (.inl (a, j))

theorem movingPatternFiniteSamples_units {B C : Type*} {N n q : ℕ} [Fact q.Prime]
    (e : Fin (N + 1) ≃ B ⊕ C) (value : Fin (N + 1) → ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (h : ∀ c, (value (e.symm (.inr c)) : ZMod q) ≠ 0) (b : Bool) :
    ((movingPatternFiniteSamples e n pattern b).values value).UnitsAt q := by
  apply MovingSampleSlots.values_units_of_coordinates
  intro i
  simpa only [movingPatternFiniteSamples, movingPatternSamples, Equiv.apply_symm_apply,
    Function.comp_apply] using h (pattern (b, i))

theorem movingPatternFiniteSmall_unit {B C : Type*} {N n q : ℕ} [Fact q.Prime]
    (e : Fin (N + 1) ≃ B ⊕ C) (value : Fin (N + 1) → ℕ)
    (small : TreeLeafTuple (List B) n)
    (h : ∀ b ∈ flattenMovingSlots n small, (value (e.symm (.inl b)) : ZMod q) ≠ 0) :
    ((treeLeafProduct n (movingSlotValues value n (movingPatternFiniteSmall e n small)) : ℕ) : ZMod q) ≠ 0 := by
  apply movingSlotValues_unit
  intro i hi
  rw [movingPatternFiniteSmall, flattenMovingSlots_map] at hi
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
  exact h b hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternWindowGain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform quartet gain for the actual moving Fourier windows -/

namespace Ostmann
open scoped SchwartzMap

/-- The tolerance is selected after the fixed Fourier profile and frequency
cost, and before the bulk length. All sharp cutoffs are included in `W`. -/
theorem exists_movingPatternKernelGain_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A H B D F gain : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) → ∀ amp δ : ℝ,
      0 ≤ amp → amp ≤ Real.exp (F * m) → 0 ≤ δ →
      δ ≤ signedBulkGainTarget n (C + F) gain →
      let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      (W * amp) * 4 ^ Fintype.card (TreeLeafIndex n × Fin m) * δ ^ m ≤
        Real.exp (-gain * m) := by
  obtain ⟨C, hC, hcost⟩ := movingPatternKernelBudget_exp_window ψ n r₀ A H B D hA hH
  refine ⟨2 * C, by positivity, ?_⟩
  intro m hm lo hi hhi hwidth amp δ hamp hampBound hδ hgain
  dsimp only
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hW : 0 ≤ W := sq_nonneg _
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hWbound : W ≤ Real.exp (2 * C * m) := by
    apply (bulkKernelPair_smooth_le_budget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D).trans
    apply (hcost m lo hi hhi hwidth).trans
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hamp' : W * amp ≤ Real.exp ((2 * C + F) * m) := by
    apply (mul_le_mul hWbound hampBound hamp (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  have h := signedBulkGainTarget_bound n m (2 * C + F) gain 1 (W * amp) δ
    (by norm_num) (mul_nonneg hW hamp) hδ hamp' hgain
  simpa only [one_mul] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternWindowPrimeGain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A window-uniform local tolerance for the literal prime comparison -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- A single mixed-character tolerance and prime threshold work for all
actual pattern trees and bulk lengths. No local cancellation bound is an
assumption here: it is derived from the quartet theorem. -/
theorem exists_movingPatternPrimeGain_window_oai (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A H B D F gain : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ ε δ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) → ∀ (Bidx Cidx : Type) (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (base : Fin (N + 1) → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime],
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0 ∧ s.natAbs < p i) →
      (∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
        (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0) →
      (∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0) →
      ∀ (twist : ∀ i, Bool → (ZMod (p i))ˣ)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m)),
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      ∀ S : ∀ i, Finset (ZMod (p i)),
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i)) →
      (∀ i, residueDensity (S i) ≤ 2 / 3) →
      (∀ i, (S i).Nonempty) → (∀ i, (S i).card < p i) →
      ∀ β : Fin m → ℝ, (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((S i).card : ℂ)⁻¹ * ∑ x ∈ S i, χ⁻¹ (-a - x)‖ ≤ β i) →
      ∀ amp : ℝ, 0 ≤ amp → amp ≤ Real.exp (F * m) →
      let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
      (∀ i, ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ) : ℂ)⁻¹ *
          ∑ z, frozenBulkSpectatorHaar base (n + 2) m t
            (fun b => movingPatternFiniteSmall e (n + 2) (small b))
            (movingPatternFiniteSamples e (n + 2) pattern) (twist i) perm
            (normalizedResidueTransform (S i)) z‖ ≤ δ) ∧
        (W * amp) * 4 ^ Fintype.card (TreeLeafIndex (n + 2) × Fin m) *
          δ ^ m ≤ Real.exp (-gain * m) := by
  obtain ⟨C, _, hkernel⟩ := exists_movingPatternKernelGain_window ψ (n + 2) r₀
    A H B D F gain hA hH
  obtain ⟨ε, hε, hε1, cutoff, hcutoff, hlocal⟩ := exists_frozenSpectatorGain n (C + F) gain
  let δ := signedBulkGainTarget (n + 2) (C + F) gain
  refine ⟨ε, δ, hε, hε1, signedBulkGainTarget_pos _ _ _, cutoff, hcutoff, ?_⟩
  intro m hm lo hi hhi hwidth Bidx Cidx N e base t small pattern p _ hp hfreq hsmall hsamples twist perm hgood
    S hlo hupper hS hSp β hβ hbias amp hamp hampBound
  dsimp only
  have hlocalBound (i : Fin m) :
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ) : ℂ)⁻¹ *
        ∑ z, frozenBulkSpectatorHaar base (n + 2) m t
          (fun b => movingPatternFiniteSmall e (n + 2) (small b))
          (movingPatternFiniteSamples e (n + 2) pattern) (twist i) perm
          (normalizedResidueTransform (S i)) z‖ ≤ δ :=
    hlocal (p i) (hp i) (Fin (N + 1)) base m (by omega) t _ _
      (fun b => movingGiantFrequencyUnits_of_bounds (t b) (hfreq i b))
      (fun b => movingPatternFiniteSmall_unit e base (small b) (hsmall i b))
      (movingPatternFiniteSamples_units e base pattern (hsamples i))
      (twist i) perm hgood (S i) (hlo i) (hupper i) (hS i) (hSp i) (β i) (hβ i) (hbias i)
  exact ⟨hlocalBound, hkernel m hm lo hi hhi hwidth amp δ hamp hampBound
    (signedBulkGainTarget_pos _ _ _).le le_rfl⟩

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.exists_movingPatternPrimeGain_window_oai := @OAI.Ostmann.exists_movingPatternPrimeGain_window_oai
