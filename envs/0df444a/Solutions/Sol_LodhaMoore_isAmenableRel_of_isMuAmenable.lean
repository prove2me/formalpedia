-- Prove2me | solution 1 for LodhaMoore.isAmenableRel_of_isMuAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T06:31:34.889722+00:00
-- url     : https://prove2.me/submissions/9aa9675b-d98d-48fa-85b1-14708022910b

import Mathlib
import Definitions.Def_ThompsonAmenability
import Theorems.Thm_Monod_isAmenableRel_orbit_of_isAmenable
import Theorems.Thm_Garrido_isAmenable_of_commGroup
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_CannonFloydParry
import Definitions.Def_Garrido_Amenability

section
section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-!
# Blueprint: Monod 2023, Theorem 5.1

`H_ℚ(ℤ)` (`Monod.HRat`) is not co-amenable in `H_ℚ(ℚ)` (`HB ratSubring Monod.ratPoints`) nor in
`H^{C¹}_ℚ(ℚ)` (`HC1RatRat`).

Route (Monod 2023, Theorem 4.6, "the same statement holds with Γ∅ replaced throughout by
Thompson's group", and Proposition 4.7):
* Part A — the containments `HRat ≤ HC1RatRat ≤ HB ratSubring ratPoints`.
* Part B — every element of `HB ratSubring ratPoints` agrees with a Möbius map of `SL₂(ℚ)` at each
  irrational point and preserves Lebesgue-null sets.
* Part C — cut-and-paste: one explicit element of `HRat` realises `x ↦ -1/x` on `(1, 2)`; with the
  rational affine maps (in `HC1RatRat`) it realises every `g ∈ SL₂(ℚ)` at every irrational point.
* Part D — relative Zimmer (Monod 2023, Proposition 4.7), for means: if `Γ ≤ Λ` is co-amenable and
  the `Γ`-orbit relation is amenable, then so is any relation `R` that agrees with the `Λ`-orbit
  relation on a conull saturated set.
* Part E — the orbit relation of `HRat` on `P¹` is amenable: via the published conjugacy of `HRat`
  with Thompson's `F` on `(0,1)`, it is the orbit relation of the amenable dyadic affine group.
* Assembly — co-amenability would make the `SL₂(ℚ)` orbit relation amenable, contradicting
  `Monod.not_isAmenableRel_mob` (Carrière–Ghys, the dense subring `ℚ`).
-/
/-- Homeomorphisms of `P¹`. -/
abbrev Hom := OnePoint ℝ ≃ₜ OnePoint ℝ

/-- Homeomorphisms of `P¹` act on `P¹` by evaluation. -/
instance instMulActionHom : MulAction Hom (OnePoint ℝ) where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- `SL₂(ℚ)`, with `ℚ` as the subring `ratSubring` of `ℝ`. -/
abbrev SLQ := Matrix.SpecialLinearGroup (Fin 2) ratSubring

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
/-!
# Monod 2023, Theorem 5.1 — Part A (and Part E3)

* The containments `HRat ≤ HC1RatRat ≤ HB ratSubring ratPoints`, and `HRat ≤ HB ratSubring ratPoints`.
* `ratSubring` is countable and dense; `volP1` is σ-finite.
* Part E3: amenability of a measured relation passes to a relation that agrees with it on a
  conull set saturated for the new relation.
-/
/-! ## Containments -/

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part A: containments and the subring `ℚ` -/

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
/-! ## The subring `ℚ` -/

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
variable {A : Subring ℝ}
/-!
# Monod 2023, Theorem 5.1 — Part B: elements of `H_ℚ(ℚ)` at irrational points

* `X0ᶜ = {∞} ∪ ℚ` is countable, hence measurable and `volP1`-null.
* A Möbius map with rational entries preserves the irrational points (and so does its inverse).
* Every generator of `H_ℚ(ℚ)` agrees at every point of `P¹` with a Möbius map of `SL₂(ℚ)`: off the
  breakpoints by definition, and at a breakpoint by the identity theorem on an adjacent interval
  free of breakpoints together with continuity. Closure induction then gives
  `exists_mob_of_mem_HB`.
* Möbius maps are smooth off their pole, so they pull null sets back to null sets; an element of
  `H_ℚ(ℚ)` pulls a null set back into `X0ᶜ` union countably many Möbius preimages.

The basic Möbius facts (formulas, group law, continuity, identity theorem) are adapted from
`Solutions/Monod/DynBasic.lean`, `DynGerm.lean`, `RedMob.lean` and `RedNull.lean`.
-/
/-! ### Möbius maps: formulas, group law, continuity -/

/-! ### Identity theorem -/

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
/-! ### The subring `ℚ` and `SL₂(ℚ)` are countable -/
instance countable_ratSubring' : Countable ratSubring := by
  have hs : Function.Surjective (fun q : ℚ => (⟨(q : ℝ), RingHom.mem_range_self _ q⟩ : ratSubring)) := by
    rintro ⟨x, hx⟩
    obtain ⟨q, rfl⟩ := RingHom.mem_range.1 hx
    exact ⟨q, rfl⟩
  exact hs.countable

instance countable_SLQ : Countable SLQ :=
  inferInstanceAs (Countable {M : Fin 2 → Fin 2 → ratSubring // Matrix.det M = 1})

/-! ### The irrational points -/

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part B: elements of `H_ℚ(ℚ)` at irrational points -/

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
/-! ### Elements of `H_ℚ(ℚ)` at irrational points -/

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB
/-! ### Null sets -/

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology OnePoint Set
namespace ThompsonAmenability.M51.PartB

end ThompsonAmenability.M51.PartB
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open Filter Topology Set OnePoint
namespace ThompsonAmenability.M51.PartC
variable {A : Subring ℝ}
/-!
# Part C: cut-and-paste

One explicit element `hS` of `H_ℚ(ℤ)` realises `y ↦ -1/y` on `(1, 2]`: it is the order
automorphism `psi` of `ℝ` (pieces `y - 2`, `-1/y`, `(y - 3)/(4 - y)`, `y - 3`, breakpoints `1, 2, 3`,
all in `SL₂(ℤ)`), extended to `P¹` fixing `∞`. With the rational affine maps
`aff a b : t ↦ a² t + a b` (Möbius maps of `!![a, b; 0, a⁻¹] ∈ SL₂(ℚ)`, in `H^{C¹}_ℚ(ℚ)`) it realises
`y ↦ -1/y` at every `y ≠ 0`, and then every `g ∈ SL₂(ℚ)` at every irrational point:
`g = τ_{a/c} ∘ S ∘ A_{c,d}` when `c ≠ 0`, `g = A_{a,b}` when `c = 0`.
-/
/-! ### Möbius maps: entries and formulas -/

/-! ### Order automorphisms of `ℝ`, extended to `P¹` -/

/-! ### The element `hS` -/

/-! ### The rational affine maps -/

/-! ### The countable subgroup `CC` -/

/-! ### Realising `y ↦ -1/y` -/

/-! ### Every `g ∈ SL₂(ℚ)` at every irrational point -/

end ThompsonAmenability.M51.PartC
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part C: cut-and-paste -/

end ThompsonAmenability.M51
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {X : Type*} (m : Set X → ℝ≥0∞)
/-!
# Part D: relative Zimmer (Monod 2023, Proposition 4.7), for means

If `Γ ≤ Λ` is co-amenable and the `Γ`-orbit relation is amenable, then any relation `R` agreeing
with the `Λ`-orbit relation on a conull saturated set (realised there by a countable set `C`) is
amenable.

Route.  After replacing `μ` by an equivalent finite measure:
* the invariant finitely additive probability on `Q = Λ ⧸ Γ` gives a mean `Mn` on bounded
  functions on `Q` (the upper Darboux integral, as in `MEAN_Bridge.lean`);
* for `λ ∈ Λ` and `g` bounded on `R` over `X₀`, `Fl λ g := P_Γ (g_λ) ∘ λ⁻¹`, where
  `g_λ (w, z) = g (λ w, z)` for `λ w ∈ X₀` (and `0` otherwise); up to null sets it depends only on
  the coset `λ Γ`;
* `P g ∈ L²(μ)` is the Riesz representative of `h ↦ Mn (q ↦ ⟪Fl (rep q) g, h⟫)`;
* the axioms follow from those of `P_Γ`; translation invariance `P (g ∘ κ⁻¹) = (P g) ∘ κ⁻¹`
  from the invariance of `Mn` under `Λ`; invariance under an arbitrary partial transformation
  `φ` from translation invariance and locality, on the countably many measurable pieces
  `{y | P g (φ⁻¹ y) = P g (κ⁻¹ y), g (φ⁻¹ y, c y) = g (κ⁻¹ y, c y) ∀ c ∈ C}`, `κ ∈ C`.
-/
/-! ## The mean on a set with a finitely additive probability (after `MEAN_Bridge.lean`) -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {X : Type*} (m : Set X → ℝ≥0∞)
variable {m}

/-! ### The upper integral on `ℓ∞` -/
local notation "E" X => lp (fun _ : X => ℝ) ∞

/-- A finitely valued function as an element of `ℓ∞`. -/
noncomputable def meanOfFin (s : X → ℝ) (hs : (range s).Finite) : E X :=
  ⟨s, memℓp_infty_iff.2 (by
    have : (range fun i => ‖s i‖) = (fun v => ‖v‖) '' range s := by
      rw [← Set.range_comp]; rfl
    rw [this]
    exact (hs.image _).bddAbove)⟩

@[simp] theorem meanOfFin_apply (s : X → ℝ) (hs : (range s).Finite) (x : X) :
    (meanOfFin s hs : X → ℝ) x = s x := rfl

theorem mean_range_indicator (A : Set X) : (range (A.indicator (1 : X → ℝ))).Finite :=
  (Set.toFinite ({0, 1} : Set ℝ)).subset (by
    rintro _ ⟨x, rfl⟩; by_cases h : x ∈ A <;> simp [h])

/-- The indicator function of `A` as an element of `ℓ∞`. -/
noncomputable def mean_ind (A : Set X) : E X := meanOfFin _ (mean_range_indicator A)

@[simp] theorem mean_ind_apply (A : Set X) (x : X) :
    (mean_ind A : X → ℝ) x = A.indicator 1 x := rfl

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {Q : Type*}
/-! ### The mean as a function on bounded functions -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {Q : Type*}
variable {m} (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
include hm h1

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
open Monod
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
/-! ## Generic facts about left invariant means -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
open Monod
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {R : Set (X × X)} {P : (X × X → ℝ) → X → ℝ}

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
open Monod
variable {X : Type*} [MeasurableSpace X] {R : Set (X × X)} (φ : PartialTransformation R)
/-! ## Partial transformations -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
/-! ## Integration helpers -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-! ## Riesz representation -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
/-! ## The data of the relative Zimmer theorem -/

end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
namespace Data
open Monod Classical
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : Type*} [Group G] [MulAction G X]

end Data
end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
namespace Data
open Monod Classical
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : Type*} [Group G] [MulAction G X]
variable {g g' : X × X → ℝ} {C C' : ℝ}
/-! ### The functions `F_λ` -/

end Data
end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
namespace Data
open Monod Classical
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : Type*} [Group G] [MulAction G X]
variable [IsFiniteMeasure μ] {g g' : X × X → ℝ} {C C' : ℝ}
/-! ### The mean `P` -/

/-! ### The axioms of a mean -/

/-! ### Invariance under the partial transformations of `R` -/

end Data
end ThompsonAmenability.M51.PartD
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
namespace ThompsonAmenability.M51.PartD
open Garrido
/-! ## The theorem -/

end ThompsonAmenability.M51.PartD
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part D: relative Zimmer (Monod 2023, Proposition 4.7) -/

/-! ## Part E1: Thompson's group `F` at non-dyadic points -/

end ThompsonAmenability.M51
end

section
namespace ThompsonAmenability.M51.PartE1
open CannonFloydParry
/-!
# Part E1: Thompson's group `F` at non-dyadic points

* `F_apply_nonDyadic_daff`: at a non-dyadic point `t ∈ (0,1)` an element of `F` acts by a dyadic
  affine map `y ↦ 2ⁿ y + c` (`c` dyadic), and the image is again non-dyadic in `(0,1)`.
* `exists_F_of_daff`: two non-dyadic points of `(0,1)` related by a dyadic affine map lie in one
  `F`-orbit: glue the affine map on a small dyadic interval around `t` to an element of `F` that
  agrees with it at the two endpoints (`exists_mem_F_map_partition`).
-/
/-! ### Dyadic rationals -/

/-! ### Gaps in a finite set -/

/-! ### `extend` -/

/-! ### Target 1 -/

end ThompsonAmenability.M51.PartE1
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
namespace ThompsonAmenability.M51.PartE1
open CannonFloydParry
/-! ### Gluing an affine piece into an element of `F` -/

/-! ### Target 2 -/

end ThompsonAmenability.M51.PartE1
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
/-!
# Part E2: the orbit relation of `H_ℚ(ℤ)` on `P¹` is amenable

Route. The published conjugacy `Monod.contDiff_and_exists_mulEquiv_HRat_F` gives `c` (strictly
monotone from `(0,1)` onto `ℝ`) and `φ : HRat ≃* F` with `h (c t) = c (extend (φ h) t)`.
* `alpha : ℝ → (0,1)` is an increasing bijection that is dyadic affine on every `[n, n+1]`
  (`alpha y = 2^e y + b`, `b` dyadic), so `Psi := c ∘ alpha` is an order isomorphism of `ℝ`.
* `Aff` is the group of dyadic affine maps `y ↦ 2ⁿ y + b` of `ℝ`: countable and solvable, hence
  amenable; it acts on `P¹` through `Psi` (the subgroup `Lam` of homeomorphisms of `P¹`).
* On the conull set `X1 = c '' (non-dyadic points)`, the `Lam`-orbits and the `HRat`-orbits
  coincide (Blueprint `F_apply_nonDyadic_daff`, `exists_F_of_daff`), so `Lam` preserves null sets
  (Blueprint `exists_mob_of_mem_HB`, `null_preimage_mob`), the published C1 theorem makes the
  `Lam`-orbit relation amenable, and the Blueprint's `isAmenableRel_of_agree` transfers it.
-/
/-! ## Section 1: dyadic rationals -/
lemma isDyadic_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma isDyadic_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma isDyadic_zpow_mul {n : ℤ} {x : ℝ} (hx : IsDyadic x) : IsDyadic (2 ^ n * x) := by
  obtain ⟨m, k, rfl⟩ := hx
  by_cases hn : 0 ≤ n
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine ⟨m * 2 ^ j, k, ?_⟩
    push_cast
    rw [zpow_natCast]
    ring
  · push Not at hn
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j : ℤ) := ⟨(-n).toNat, by omega⟩
    refine ⟨m, k + j, ?_⟩
    rw [zpow_neg, zpow_natCast]
    field_simp
    ring

lemma isDyadic_intCast (m : ℤ) : IsDyadic (m : ℝ) := ⟨m, 0, by simp⟩

lemma isDyadic_zero : IsDyadic 0 := by simpa using isDyadic_intCast 0

lemma isDyadic_zpow (n : ℤ) : IsDyadic ((2 : ℝ) ^ n) := by
  simpa using isDyadic_zpow_mul (n := n) (isDyadic_intCast 1)

lemma countable_isDyadic : {x : ℝ | IsDyadic x}.Countable := by
  have : {x : ℝ | IsDyadic x} = Set.range (fun p : ℤ × ℕ => (p.1 : ℝ) / 2 ^ p.2) := by
    ext x
    simp only [Set.mem_range, Prod.exists, IsDyadic]
    constructor
    · rintro ⟨m, k, rfl⟩; exact ⟨m, k, rfl⟩
    · rintro ⟨m, k, rfl⟩; exact ⟨m, k, rfl⟩
  rw [this]
  exact Set.countable_range _

/-! ## Section 2: the dyadic affine relation `DAff` -/

/-! ## Section 3: the increasing dyadic bijection `alpha : ℝ → (0,1)` -/
/-- The knots: `2^(n-1)` for `n ≤ 0`, `1 - 2^(-n-1)` for `n ≥ 0`. -/
noncomputable def knot (n : ℤ) : ℝ := if n ≤ 0 then 2 ^ (n - 1) else 1 - 2 ^ (-n - 1)

/-- The exponent of the slope on `[n, n+1]`. -/
def ex (n : ℤ) : ℤ := if n < 0 then n - 1 else -n - 2

lemma knot_succ (n : ℤ) : knot (n + 1) = knot n + 2 ^ ex n := by
  unfold knot ex
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [if_pos (by omega), if_pos hn.le, if_pos hn]
    have : n + 1 - 1 = (n - 1) + 1 := by ring
    rw [this, zpow_add_one₀ two_ne_zero]
    ring
  · norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have h1 : -(n + 1) - 1 = -n - 2 := by ring
    have h2 : -n - 1 = (-n - 2) + 1 := by ring
    rw [h1, h2, zpow_add_one₀ two_ne_zero]
    ring

lemma knot_pos (n : ℤ) : 0 < knot n := by
  unfold knot
  split_ifs with h
  · positivity
  · have : (2 : ℝ) ^ (-n - 1) < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by omega)
    linarith

lemma knot_lt_one (n : ℤ) : knot n < 1 := by
  unfold knot
  split_ifs with h
  · exact zpow_lt_one_of_neg₀ (by norm_num) (by omega)
  · have : (0 : ℝ) < 2 ^ (-n - 1) := by positivity
    linarith

lemma knot_strictMono : StrictMono knot :=
  strictMono_int_of_lt_succ fun n => by rw [knot_succ]; linarith [zpow_pos (two_pos (α := ℝ)) (ex n)]

/-- The increasing bijection `ℝ → (0,1)`, affine with slope `2 ^ ex n` on `[n, n+1]`. -/
noncomputable def alpha (y : ℝ) : ℝ := knot ⌊y⌋ + (y - ⌊y⌋) * 2 ^ ex ⌊y⌋

lemma knot_le_alpha (y : ℝ) : knot ⌊y⌋ ≤ alpha y := by
  unfold alpha
  have := Int.floor_le y
  have : (0 : ℝ) < 2 ^ ex ⌊y⌋ := by positivity
  nlinarith

lemma alpha_lt_knot (y : ℝ) : alpha y < knot (⌊y⌋ + 1) := by
  unfold alpha
  rw [knot_succ]
  have := Int.lt_floor_add_one y
  have : (0 : ℝ) < 2 ^ ex ⌊y⌋ := by positivity
  nlinarith

lemma alpha_strictMono : StrictMono alpha := by
  intro y z hyz
  rcases (Int.floor_mono hyz.le).eq_or_lt with h | h
  · unfold alpha
    rw [h]
    have : (0 : ℝ) < 2 ^ ex ⌊z⌋ := by positivity
    nlinarith
  · calc alpha y < knot (⌊y⌋ + 1) := alpha_lt_knot y
      _ ≤ knot ⌊z⌋ := knot_strictMono.monotone (by omega)
      _ ≤ alpha z := knot_le_alpha z

lemma alpha_mem (y : ℝ) : alpha y ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨(knot_pos _).trans_le (knot_le_alpha y), (alpha_lt_knot y).trans (knot_lt_one _)⟩

lemma alpha_surj {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : ∃ y, alpha y = t := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr ht1) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨k', hk'⟩ := exists_pow_lt_of_lt_one ht0 (by norm_num : (1 / 2 : ℝ) < 1)
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, knot z ≤ t → z ≤ b := by
    refine ⟨k, fun z hz => ?_⟩
    by_contra hzk
    push Not at hzk
    have hz0 : ¬ z ≤ 0 := by omega
    unfold knot at hz
    rw [if_neg hz0] at hz
    have : (2 : ℝ) ^ (-z - 1) ≤ (1 / 2) ^ k := by
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  have hne : ∃ z : ℤ, knot z ≤ t := by
    refine ⟨-(k' : ℤ), ?_⟩
    unfold knot
    rw [if_pos (by omega)]
    have : (2 : ℝ) ^ (-(k' : ℤ) - 1) ≤ (1 / 2) ^ k' := by
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  have hlt : t < knot (n + 1) := by
    by_contra h
    push Not at h
    have := hmax _ h
    omega
  rw [knot_succ] at hlt
  have hpos : (0 : ℝ) < 2 ^ ex n := by positivity
  set y : ℝ := n + (t - knot n) / 2 ^ ex n with hy
  have hfl : ⌊y⌋ = n := by
    rw [Int.floor_eq_iff]
    constructor
    · have : 0 ≤ (t - knot n) / 2 ^ ex n := div_nonneg (by linarith) hpos.le
      linarith
    · have : (t - knot n) / 2 ^ ex n < 1 := by rw [div_lt_one hpos]; linarith
      linarith
  refine ⟨y, ?_⟩
  unfold alpha
  rw [hfl, hy]
  field_simp
  ring

/-! ## Section 4: the dyadic affine group `Aff` -/
/-- `y ↦ 2ⁿ y + b` as an order isomorphism of `ℝ`. -/
noncomputable def affIso (n : ℤ) (b : ℝ) : ℝ ≃o ℝ :=
  (OrderIso.mulLeft₀ ((2 : ℝ) ^ n) (by positivity)).trans (OrderIso.addRight b)

@[simp] lemma affIso_apply (n : ℤ) (b y : ℝ) : affIso n b y = 2 ^ n * y + b := rfl

/-- A dyadic affine map `y ↦ 2ⁿ y + b`, `b` dyadic. -/
def IsDAffMap (f : ℝ ≃o ℝ) : Prop := ∃ (n : ℤ) (b : ℝ), IsDyadic b ∧ ∀ y, f y = 2 ^ n * y + b

/-- The dyadic affine group. -/
def Aff : Subgroup (ℝ ≃o ℝ) where
  carrier := {f | IsDAffMap f}
  mul_mem' := by
    rintro f g ⟨n, b, hb, hf⟩ ⟨m, b', hb', hg⟩
    refine ⟨n + m, 2 ^ n * b' + b, isDyadic_add (isDyadic_zpow_mul hb') hb, fun y => ?_⟩
    rw [RelIso.mul_apply, hg, hf, zpow_add₀ two_ne_zero]
    ring
  one_mem' := ⟨0, 0, isDyadic_zero, fun y => by simp [RelIso.one_apply]⟩
  inv_mem' := by
    rintro f ⟨n, b, hb, hf⟩
    refine ⟨-n, -(2 ^ (-n) * b), isDyadic_neg (isDyadic_zpow_mul hb), fun y => ?_⟩
    apply f.injective
    rw [RelIso.apply_inv_self, hf]
    have h2 : (2 : ℝ) ^ n * 2 ^ (-n) = 1 := by rw [← zpow_add₀ two_ne_zero]; simp
    linear_combination (b - y) * h2

lemma isDyadic_apply_zero (f : Aff) : IsDyadic ((f : ℝ ≃o ℝ) 0) := by
  obtain ⟨n, b, hb, hf⟩ := f.2
  rw [hf]; simpa using hb

lemma isDyadic_apply_one (f : Aff) : IsDyadic ((f : ℝ ≃o ℝ) 1) := by
  obtain ⟨n, b, hb, hf⟩ := f.2
  rw [hf, mul_one]; exact isDyadic_add (isDyadic_zpow n) hb

instance countable_Aff : Countable Aff := by
  have : Countable {x : ℝ // IsDyadic x} := countable_isDyadic.to_subtype
  refine Function.Injective.countable
    (f := fun f : Aff => ((⟨_, isDyadic_apply_zero f⟩ : {x : ℝ // IsDyadic x}),
      (⟨_, isDyadic_apply_one f⟩ : {x : ℝ // IsDyadic x}))) ?_
  intro f g hfg
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hfg
  obtain ⟨n, b, -, hf⟩ := f.2
  obtain ⟨m, b', -, hg⟩ := g.2
  rw [hf, hf, hg, hg] at hfg
  apply Subtype.ext; ext y
  rw [hf, hg]
  have hb : b = b' := by simpa using hfg.1
  have hn : (2 : ℝ) ^ n = 2 ^ m := by linarith [hfg.2]
  rw [hb, hn]

/-! ## Section 5: the conjugated action on `P¹` -/
/-- The data of the published conjugacy of `HRat` with Thompson's group `F`. -/
structure Conj where
  c : ℝ → ℝ
  mono : StrictMonoOn c (Set.Ioo 0 1)
  surj : c '' Set.Ioo 0 1 = Set.univ
  φ : Monod.HRat ≃* CannonFloydParry.F
  hφ : ∀ (h : Monod.HRat), ∀ t ∈ Set.Ioo (0 : ℝ) 1,
    (h : OnePoint ℝ ≃ₜ OnePoint ℝ) (c t : OnePoint ℝ) =
      (c (CannonFloydParry.extend (φ h : CannonFloydParry.UI ≃o CannonFloydParry.UI) t) :
        OnePoint ℝ)

end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
namespace Conj
variable (K : Conj)
lemma exists_eq (r : ℝ) : ∃ t ∈ Set.Ioo (0 : ℝ) 1, K.c t = r := by
  have : r ∈ K.c '' Set.Ioo 0 1 := by rw [K.surj]; trivial
  exact this

lemma psi_strictMono : StrictMono (K.c ∘ alpha) := fun _ _ h =>
  K.mono (alpha_mem _) (alpha_mem _) (alpha_strictMono h)

lemma psi_surj : Function.Surjective (K.c ∘ alpha) := by
  intro r
  obtain ⟨t, ht, rfl⟩ := K.exists_eq r
  obtain ⟨y, rfl⟩ := alpha_surj ht
  exact ⟨y, rfl⟩

/-- `Psi = c ∘ alpha`, an order isomorphism of `ℝ`. -/
noncomputable def Psi : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ K.psi_strictMono K.psi_surj

/-- Conjugation by `Psi`, then extension to `P¹`. -/
noncomputable def rho : (ℝ ≃o ℝ) →* Hom where
  toFun f := Homeomorph.onePointCongr (K.Psi.symm.trans (f.trans K.Psi)).toHomeomorph
  map_one' := by
    ext x
    induction x using OnePoint.rec <;> simp
  map_mul' f g := by
    ext x
    induction x using OnePoint.rec <;> simp

/-- The dyadic affine group acting on `P¹` through `Psi`. -/
noncomputable def Lam : Subgroup Hom := Aff.map K.rho

instance countable_Lam : Countable K.Lam :=
  (K.rho.subgroupMap_surjective Aff).countable

end Conj
end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
/-! ## Section 5b: `SL₂(ℚ)` is countable -/

/-! ## Section 6: the conull set `X1 = c '' (non-dyadic points)` -/
lemma volP1_singleton (x : OnePoint ℝ) : Monod.volP1 {x} = 0 := by
  unfold Monod.volP1
  rw [Measure.map_apply OnePoint.continuous_coe.measurable (measurableSet_singleton x)]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  exact OnePoint.coe_injective (ha.trans hb.symm)

instance : NullSingletonClass Monod.volP1 := ⟨volP1_singleton⟩

end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
namespace Conj
variable (K : Conj)

/-! ## Section 7: on `X1` the two orbit relations agree -/

/-! ## Section 8: `Lam` preserves null sets -/

end Conj
end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
/-! ## `volP1` is σ-finite -/

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
variable {X : Type*}
/-! ## Part E3: relations agreeing on a conull saturated set -/
/-- Cut a function on `X × X` down to the pairs with first coordinate in `X₁`. -/
noncomputable def cut (X₁ : Set X) (f : X × X → ℝ) : X × X → ℝ :=
  (Prod.fst ⁻¹' X₁).indicator f

theorem cut_of_mem {X₁ : Set X} (f : X × X → ℝ) {p : X × X} (hp : p.1 ∈ X₁) :
    cut X₁ f p = f p :=
  Set.indicator_of_mem (show p ∈ Prod.fst ⁻¹' X₁ from hp) f

theorem cut_of_notMem {X₁ : Set X} (f : X × X → ℝ) {p : X × X} (hp : p.1 ∉ X₁) :
    cut X₁ f p = 0 :=
  Set.indicator_of_notMem (show p ∉ Prod.fst ⁻¹' X₁ from hp) f

theorem isBddMeasOn_cut [MeasurableSpace X] {R R' : Set (X × X)} {X₁ : Set X} (hX₁ : MeasurableSet X₁)
    (hagree : ∀ x ∈ X₁, ∀ y, (x, y) ∈ R ↔ (x, y) ∈ R') {f : X × X → ℝ}
    (hf : Monod.IsBddMeasOn R' f) : Monod.IsBddMeasOn R (cut X₁ f) := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm.indicator (measurable_fst hX₁), max C 0, fun p hp => ?_⟩
  by_cases h1 : p.1 ∈ X₁
  · rw [cut_of_mem f h1]
    exact (hC p ((hagree p.1 h1 p.2).1 hp)).trans (le_max_left _ _)
  · rw [cut_of_notMem f h1, abs_zero]
    exact le_max_right _ _

/-- A partial transformation of `R'`, restricted to `X₁`, is a partial transformation of `R`. -/
noncomputable def restrictPT [MeasurableSpace X] {R R' : Set (X × X)} {X₁ : Set X} (hX₁ : MeasurableSet X₁)
    (hsat : ∀ p ∈ R', (p.1 ∈ X₁ ↔ p.2 ∈ X₁))
    (hagree : ∀ x ∈ X₁, ∀ y, (x, y) ∈ R ↔ (x, y) ∈ R')
    (φ : Monod.PartialTransformation R') : Monod.PartialTransformation R where
  dom := φ.dom ∩ X₁
  cod := φ.cod ∩ X₁
  measurableSet_dom := φ.measurableSet_dom.inter hX₁
  measurableSet_cod := φ.measurableSet_cod.inter hX₁
  e :=
    { toFun := fun a => ⟨φ.e ⟨a, a.2.1⟩, (φ.e ⟨a, a.2.1⟩).2,
        (hsat _ (φ.graph_subset ⟨a, a.2.1⟩)).1 a.2.2⟩
      invFun := fun b => ⟨φ.e.symm ⟨b, b.2.1⟩, (φ.e.symm ⟨b, b.2.1⟩).2, by
        have := hsat _ (φ.graph_subset (φ.e.symm ⟨b, b.2.1⟩))
        simp only [MeasurableEquiv.apply_symm_apply] at this
        exact this.2 b.2.2⟩
      left_inv := fun a => by
        apply Subtype.ext
        simp
      right_inv := fun b => by
        apply Subtype.ext
        simp
      measurable_toFun := by
        refine Measurable.subtype_mk ?_
        exact measurable_subtype_coe.comp
          (φ.e.measurable.comp measurable_subtype_coe.subtype_mk)
      measurable_invFun := by
        refine Measurable.subtype_mk ?_
        exact measurable_subtype_coe.comp
          (φ.e.symm.measurable.comp measurable_subtype_coe.subtype_mk) }
  graph_subset a := (hagree _ a.2.2 _).2 (φ.graph_subset ⟨a, a.2.1⟩)

theorem shiftRel_restrictPT [MeasurableSpace X] {R R' : Set (X × X)} {X₁ : Set X} (hX₁ : MeasurableSet X₁)
    (hsat : ∀ p ∈ R', (p.1 ∈ X₁ ↔ p.2 ∈ X₁))
    (hagree : ∀ x ∈ X₁, ∀ y, (x, y) ∈ R ↔ (x, y) ∈ R')
    (φ : Monod.PartialTransformation R') (f : X × X → ℝ) :
    (restrictPT hX₁ hsat hagree φ).shiftRel (cut X₁ f) = cut X₁ (φ.shiftRel f) := by
  funext p
  by_cases h1 : p.1 ∈ X₁
  · rw [cut_of_mem _ h1]
    by_cases h2 : p.1 ∈ φ.cod
    · have h12 : p.1 ∈ (restrictPT hX₁ hsat hagree φ).cod := ⟨h2, h1⟩
      simp only [Monod.PartialTransformation.shiftRel, dif_pos h12, dif_pos h2]
      have hmem := ((restrictPT hX₁ hsat hagree φ).e.symm ⟨p.1, h12⟩).2.2
      rw [cut_of_mem _ hmem]
      rfl
    · have h12 : p.1 ∉ (restrictPT hX₁ hsat hagree φ).cod := fun h => h2 h.1
      simp only [Monod.PartialTransformation.shiftRel, dif_neg h12, dif_neg h2]
  · rw [cut_of_notMem _ h1]
    have h12 : p.1 ∉ (restrictPT hX₁ hsat hagree φ).cod := fun h => h1 h.2
    simp only [Monod.PartialTransformation.shiftRel, dif_neg h12]

theorem shiftBase_restrictPT [MeasurableSpace X] {R R' : Set (X × X)} {X₁ : Set X} (hX₁ : MeasurableSet X₁)
    (hsat : ∀ p ∈ R', (p.1 ∈ X₁ ↔ p.2 ∈ X₁))
    (hagree : ∀ x ∈ X₁, ∀ y, (x, y) ∈ R ↔ (x, y) ∈ R')
    (φ : Monod.PartialTransformation R') (F : X → ℝ) {y : X} (hy : y ∈ X₁) :
    (restrictPT hX₁ hsat hagree φ).shiftBase F y = φ.shiftBase F y := by
  by_cases h2 : y ∈ φ.cod
  · have h12 : y ∈ (restrictPT hX₁ hsat hagree φ).cod := ⟨h2, hy⟩
    simp only [Monod.PartialTransformation.shiftBase, dif_pos h12, dif_pos h2]
    rfl
  · have h12 : y ∉ (restrictPT hX₁ hsat hagree φ).cod := fun h => h2 h.1
    simp only [Monod.PartialTransformation.shiftBase, dif_neg h12, dif_neg h2]

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51.PartA
theorem isAmenableRel_of_agree {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {R R' : Set (X × X)} (X₁ : Set X) (hX₁ : MeasurableSet X₁) (hX₁c : μ X₁ᶜ = 0)
    (hsat : ∀ p ∈ R', (p.1 ∈ X₁ ↔ p.2 ∈ X₁))
    (hagree : ∀ x ∈ X₁, ∀ y, (x, y) ∈ R ↔ (x, y) ∈ R')
    (h : Monod.IsAmenableRel μ R) : Monod.IsAmenableRel μ R' := by
  obtain ⟨P, hP⟩ := h
  have hae : ∀ᵐ y ∂μ, y ∈ X₁ := ae_iff.2 hX₁c
  have hbdd : ∀ f, Monod.IsBddMeasOn R' f → Monod.IsBddMeasOn R (cut X₁ f) :=
    fun f hf => isBddMeasOn_cut hX₁ hagree hf
  refine ⟨fun f => P (cut X₁ f), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro f hf
    exact hP.aemeasurable _ (hbdd f hf)
  · intro f g hf hg hfg
    refine hP.congr _ _ (hbdd f hf) (hbdd g hg) ?_
    unfold Monod.RelNull at hfg ⊢
    refine measure_mono_null ?_ hfg
    rintro x ⟨p, ⟨hp, hpR⟩, rfl⟩
    by_cases h1 : p.1 ∈ X₁
    · refine ⟨p, ⟨?_, (hagree p.1 h1 p.2).1 hpR⟩, rfl⟩
      have hp' : cut X₁ f p ≠ cut X₁ g p := hp
      rwa [cut_of_mem _ h1, cut_of_mem _ h1] at hp'
    · exact absurd (by rw [cut_of_notMem _ h1, cut_of_notMem _ h1]) hp
  · intro f g hf hg
    have : cut X₁ (f + g) = cut X₁ f + cut X₁ g := Set.indicator_add _ _ _
    show P (cut X₁ (f + g)) =ᵐ[μ] P (cut X₁ f) + P (cut X₁ g)
    rw [this]
    exact hP.add _ _ (hbdd f hf) (hbdd g hg)
  · intro c f hf
    have : cut X₁ (c • f) = c • cut X₁ f := by
      funext p
      by_cases h1 : p.1 ∈ X₁
      · rw [Pi.smul_apply, cut_of_mem _ h1, cut_of_mem _ h1]
        rfl
      · rw [Pi.smul_apply, cut_of_notMem _ h1, cut_of_notMem _ h1, smul_zero]
    show P (cut X₁ (c • f)) =ᵐ[μ] c • P (cut X₁ f)
    rw [this]
    exact hP.smul _ _ (hbdd f hf)
  · intro f hf hpos
    refine hP.nonneg _ (hbdd f hf) fun p hp => ?_
    by_cases h1 : p.1 ∈ X₁
    · rw [cut_of_mem _ h1]
      exact hpos p ((hagree p.1 h1 p.2).1 hp)
    · rw [cut_of_notMem _ h1]
  · have h1R : Monod.IsBddMeasOn R (1 : X × X → ℝ) :=
      ⟨measurable_const, 1, fun p _ => by simp⟩
    have h1R' : Monod.IsBddMeasOn R' (1 : X × X → ℝ) :=
      ⟨measurable_const, 1, fun p _ => by simp⟩
    show P (cut X₁ 1) =ᵐ[μ] 1
    refine (hP.congr _ _ (hbdd 1 h1R') h1R ?_).trans hP.one
    unfold Monod.RelNull
    refine measure_mono_null ?_ hX₁c
    rintro x ⟨p, ⟨hp, -⟩, rfl⟩ h1
    exact hp (cut_of_mem _ h1)
  · intro φ f hf
    show P (cut X₁ (φ.shiftRel f)) =ᵐ[μ] φ.shiftBase (P (cut X₁ f))
    rw [← shiftRel_restrictPT hX₁ hsat hagree φ f]
    refine (hP.invariant (restrictPT hX₁ hsat hagree φ) _ (hbdd f hf)).trans ?_
    exact hae.mono fun y hy => shiftBase_restrictPT hX₁ hsat hagree φ _ hy

end ThompsonAmenability.M51.PartA
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part E3: amenability passes between relations that agree on a conull saturated set -/
alias isAmenableRel_of_agree := ThompsonAmenability.M51.PartA.isAmenableRel_of_agree

/-! ## Assembly -/

end ThompsonAmenability.M51
end

section
open MeasureTheory Filter Topology
open CannonFloydParry (IsDyadic)
namespace ThompsonAmenability.M51.PartE2
/-! ## Section 9: assembly -/

end ThompsonAmenability.M51.PartE2
end

section
open MeasureTheory Filter Topology
namespace ThompsonAmenability.M51
/-! ## Part E2: the orbit relation of `H_ℚ(ℤ)` is amenable -/

end ThompsonAmenability.M51
end
end

section
/-!
# Lodha–Moore statement 4: a `μ`-amenable relation is amenable

Route: extend the Borel automorphism `T` of `X \ N` by the identity on `N` to a permutation `S` of
`X`; the powers of `S` give a measurable, null-set-preserving action of `Multiplicative ℤ` on `X`,
whose orbit relation is amenable by Monod C1 (ℤ is amenable, being commutative). A measurable
conull `E`-saturated set `X₁ ⊆ Nᶜ` is built by iterating null saturations (no Lusin–Novikov
needed), and on it `E` agrees with the orbit relation, so the transfer lemma
`ThompsonAmenability.M51.isAmenableRel_of_agree` finishes.
-/

open MeasureTheory

namespace LodhaMoore.Dev.Stmt4

variable {X : Type*} [MeasurableSpace X]

/-- The `E`-saturation of a set. -/
def sat (E : Set (X × X)) (A : Set X) : Set X := {y | ∃ x ∈ A, (x, y) ∈ E}

/-- Iterated measurable hulls of saturations, starting from `N`. -/
noncomputable def hull (μ : Measure X) (E : Set (X × X)) (N : Set X) : ℕ → Set X
  | 0 => N
  | k + 1 => toMeasurable μ (sat E (hull μ E N k))

lemma measurableSet_hull (μ : Measure X) (E : Set (X × X)) {N : Set X} (hN : MeasurableSet N) :
    ∀ k, MeasurableSet (hull μ E N k)
  | 0 => hN
  | _ + 1 => measurableSet_toMeasurable _ _

lemma hull_null (μ : Measure X) (E : Set (X × X)) {N : Set X} (hN : μ N = 0)
    (hqi : ∀ A : Set X, μ A = 0 → μ {y | ∃ x ∈ A, (x, y) ∈ E} = 0) :
    ∀ k, μ (hull μ E N k) = 0
  | 0 => hN
  | k + 1 => by
    simp only [hull, measure_toMeasurable]
    exact hqi _ (hull_null μ E hN hqi k)

/-- Measurability of the integer powers of a measurable equivalence. -/
lemma measurable_zpow {Y : Type*} [MeasurableSpace Y] (T : Y ≃ᵐ Y) (n : ℤ) :
    Measurable (T.toEquiv ^ n : Equiv.Perm Y) := by
  induction n using Int.induction_on with
  | zero => simpa using measurable_id
  | succ n ih =>
    rw [zpow_add_one]
    exact ih.comp T.measurable
  | pred n ih =>
    rw [zpow_sub_one]
    exact ih.comp T.symm.measurable

end LodhaMoore.Dev.Stmt4

namespace LodhaMoore

end LodhaMoore
end

section
open MeasureTheory
open LodhaMoore
open LodhaMoore.Dev.Stmt4 in
theorem solution {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (E : Set (X × X)) (hE : MeasurableSet E) (hequiv : Equivalence fun x y => (x, y) ∈ E)
    (hcount : ∀ x, {y | (x, y) ∈ E}.Countable)
    (hqi : ∀ A : Set X, μ A = 0 → μ {y | ∃ x ∈ A, (x, y) ∈ E} = 0) :
    IsMuAmenable μ E → Monod.IsAmenableRel μ E := by
  classical
  rintro ⟨N, hNm, hN0, T, hT⟩
  -- the permutation `S` of `X`: `T` on `Nᶜ`, the identity on `N`
  set S : Equiv.Perm X := Equiv.Perm.ofSubtype (p := fun x => x ∈ Nᶜ) T.toEquiv with hS
  have hSpow : ∀ n : ℤ, S ^ n = Equiv.Perm.ofSubtype (p := fun x => x ∈ Nᶜ) (T.toEquiv ^ n) :=
    fun n => (map_zpow _ _ _).symm
  have hSin : ∀ (n : ℤ) (x : X) (hx : x ∈ Nᶜ), (S ^ n) x = ((T.toEquiv ^ n) ⟨x, hx⟩ : X) := by
    intro n x hx
    rw [hSpow]
    exact Equiv.Perm.ofSubtype_apply_of_mem _ hx
  have hSout : ∀ (n : ℤ) (x : X), x ∈ N → (S ^ n) x = x := by
    intro n x hx
    rw [hSpow]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (fun h => h hx)
  -- measurability of the powers of `S`
  have hSmeas : ∀ n : ℤ, Measurable (S ^ n : Equiv.Perm X) := by
    intro n
    have heq : ((S ^ n : Equiv.Perm X) : X → X) = fun x =>
        if hx : x ∈ Nᶜ then (((T.toEquiv ^ n) ⟨x, hx⟩ : (Nᶜ : Set X)) : X)
        else (⟨x, hx⟩ : ((Nᶜ)ᶜ : Set X)).1 := by
      funext x
      by_cases hx : x ∈ Nᶜ
      · rw [dif_pos hx, hSin n x hx]
      · rw [dif_neg hx, hSout n x (by simpa using hx)]
    rw [heq]
    exact Measurable.dite (measurable_subtype_coe.comp (measurable_zpow T n))
      measurable_subtype_coe hNm.compl
  -- the action of `Multiplicative ℤ`
  let _ : MulAction (Multiplicative ℤ) X :=
    MulAction.compHom X (zpowersHom (Equiv.Perm X) S)
  have hsmul : ∀ (l : Multiplicative ℤ) (x : X), l • x = (S ^ l.toAdd) x := fun _ _ => rfl
  -- for `x ∉ N`, `x` is `E`-related to its `S`-images
  have hE_S : ∀ (n : ℤ) (x : X), x ∈ Nᶜ → (x, (S ^ n) x) ∈ E := by
    intro n x hx
    rw [hSin n x hx]
    exact (hT ⟨x, hx⟩ _).2 ⟨n, rfl⟩
  have hnull : ∀ (l : Multiplicative ℤ) (s : Set X), μ s = 0 →
      μ ((fun x : X => l • x) ⁻¹' s) = 0 := by
    intro l s hs
    refine measure_mono_null (t := N ∪ {y | ∃ x ∈ s, (x, y) ∈ E}) ?_
      (measure_union_null hN0 (hqi s hs))
    intro x hx
    simp only [Set.mem_preimage, hsmul] at hx
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · exact Or.inr ⟨_, hx, hequiv.symm (hE_S _ x hxN)⟩
  have hmeas : ∀ l : Multiplicative ℤ, Measurable (fun x : X => l • x) := fun l => by
    simpa only [hsmul] using hSmeas l.toAdd
  -- the orbit relation is amenable
  have hR : Monod.IsAmenableRel μ {p : X × X | ∃ l : Multiplicative ℤ, l • p.1 = p.2} :=
    Monod.isAmenableRel_orbit_of_isAmenable μ (Multiplicative ℤ) hmeas hnull
      (Garrido.isAmenable_of_commGroup _)
  -- a measurable null `E`-saturated set `M ⊇ N`
  set M : Set X := ⋃ k, hull μ E N k with hM
  have hMm : MeasurableSet M := MeasurableSet.iUnion (measurableSet_hull μ E hNm)
  have hM0 : μ M = 0 := measure_iUnion_null (hull_null μ E hN0 hqi)
  have hNM : N ⊆ M := Set.subset_iUnion (hull μ E N) 0
  have hsatM : ∀ x y, x ∈ M → (x, y) ∈ E → y ∈ M := by
    intro x y hx hxy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨k + 1, subset_toMeasurable _ _ ⟨x, hk, hxy⟩⟩
  have hsat : ∀ p ∈ E, (p.1 ∈ Mᶜ ↔ p.2 ∈ Mᶜ) := by
    rintro ⟨x, y⟩ hp
    simp only [Set.mem_compl_iff, not_iff_not]
    exact ⟨fun h => hsatM x y h hp, fun h => hsatM y x h (hequiv.symm hp)⟩
  have hagree : ∀ x ∈ Mᶜ, ∀ y, (x, y) ∈ {p : X × X | ∃ l : Multiplicative ℤ, l • p.1 = p.2} ↔
      (x, y) ∈ E := by
    intro x hx y
    have hxN : x ∈ Nᶜ := fun h => hx (hNM h)
    constructor
    · rintro ⟨l, hl⟩
      have hl' : (S ^ l.toAdd) x = y := hl
      rw [← hl']
      exact hE_S _ x hxN
    · intro hxy
      have hyN : y ∈ Nᶜ := fun h => (hsat _ hxy).1 hx (hNM h)
      obtain ⟨n, hn⟩ := (hT ⟨x, hxN⟩ ⟨y, hyN⟩).1 hxy
      refine ⟨Multiplicative.ofAdd n, ?_⟩
      show (S ^ n) x = y
      rw [hSin n x hxN, hn]
  exact ThompsonAmenability.M51.isAmenableRel_of_agree μ Mᶜ hMm.compl (by simpa using hM0)
    hsat hagree hR
end
