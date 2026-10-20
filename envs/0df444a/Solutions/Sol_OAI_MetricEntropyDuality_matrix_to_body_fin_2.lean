-- Prove2me | solution 2 for OAI.MetricEntropyDuality.matrix_to_body_fin
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:46:00.929705+00:00
-- url     : https://prove2.me/submissions/b7e8d6b0-f876-415d-941f-c30102d1f323

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/MatrixToBody.lean:L79-L106
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.matrix_to_body_fin. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Theorems.Thm_OAI_MetricEntropyDuality_absRowHull_symmetric
import Theorems.Thm_OAI_MetricEntropyDuality_coordinate_polar
import Theorems.Thm_OAI_MetricEntropyDuality_coverable_of_isCompact_of_mem_nhds_zero
import Theorems.Thm_OAI_MetricEntropyDuality_exists_coefficient_representatives
import Theorems.Thm_OAI_MetricEntropyDuality_mem_smul_polar_iff

-- ---- from OAI.Analysis.MetricEntropy.Basic ----
namespace OAI

universe uι uX uY

/-!
# Literal finite-dimensional convex bodies and covering numbers

The coordinate space carries its ordinary finite product topology and sup norm.
Polar membership uses the actual real coordinate pairing. Covering centers are
unrestricted ambient vectors. `coveringNumber` is the least finite cover size;
the natural-number empty-infimum convention is zero when no finite cover exists.
The geometric applications prove `Coverable` before using attainment, positivity,
or a lower bound, so that convention never substitutes for a genuine minimum.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

section Elementary

variable {ι : Type uι} {X : Type uX} {Y : Type uY} [Fintype ι]

theorem pairing_add_left (x z y : RealSpace ι) :
    pairing (x + z) y = pairing x y + pairing z y := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

theorem pairing_smul_left (a : ℝ) (x y : RealSpace ι) :
    pairing (a • x) y = a * pairing x y := by
  simp [pairing, Finset.mul_sum, mul_assoc]

theorem columnCombination_sub [Fintype Y] (g : Y → X → ℝ)
    (lam μ : RealSpace Y) :
    columnCombination g (lam - μ) = columnCombination g lam - columnCombination g μ := by
  funext x
  simp [columnCombination, sub_mul, Finset.sum_sub_distrib]

theorem pairing_row_eq_columnCombination [Fintype Y]
    (g : Y → X → ℝ) (lam : RealSpace Y) (x : X) :
    pairing (row g x) lam = columnCombination g lam x := by
  simp only [pairing, row, columnCombination, mul_comm]

end Elementary

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.ConvexBody ----
namespace OAI

universe uι uX uY

/-!
# The concrete symmetric convex bodies

The absolute row hull is the convex hull of the actual finite set of rows and
their negatives. Adding a positive multiple of the coordinate cube gives full
ambient interior, without any spanning hypothesis on the rows.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped Pointwise

section Cube

variable {ι : Type uι} [Fintype ι]

theorem cube_eq_closedBall :
    cube ι = Metric.closedBall (0 : RealSpace ι) 1 := by
  ext x
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)]
  simp only [cube, Set.mem_ofPred_eq, Real.norm_eq_abs]

theorem isCompact_cube : IsCompact (cube ι) := by
  rw [cube_eq_closedBall]
  exact isCompact_closedBall _ _

theorem convex_cube : Convex ℝ (cube ι) := by
  rw [cube_eq_closedBall]
  exact convex_closedBall _ _

omit [Fintype ι] in
theorem cube_symmetric (x : RealSpace ι) : x ∈ cube ι ↔ -x ∈ cube ι := by
  simp only [cube, Set.mem_ofPred_eq, Pi.neg_apply, abs_neg]

theorem zero_mem_interior_cube : (0 : RealSpace ι) ∈ interior (cube ι) := by
  rw [cube_eq_closedBall]
  exact Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by norm_num))

theorem cube_isSymmetricConvexBody : IsSymmetricConvexBody (cube ι) where
  isCompact := isCompact_cube
  convex := convex_cube
  symmetric := cube_symmetric
  interior_nonempty := ⟨0, zero_mem_interior_cube⟩

theorem zero_mem_interior_smul_cube {t : ℝ} (ht : t ≠ 0) :
    (0 : RealSpace ι) ∈ interior (t • cube ι) := by
  rw [interior_smul₀ ht]
  simpa only [smul_zero] using
    (Set.smul_mem_smul_set (a := t) (zero_mem_interior_cube (ι := ι)))

end Cube

section RowHull

variable {X : Type uX} {Y : Type uY} (g : Y → X → ℝ)

theorem convex_absRowHull : Convex ℝ (absRowHull g) :=
  convex_convexHull ℝ _

theorem zero_mem_absRowHull [Nonempty X] : (0 : RealSpace Y) ∈ absRowHull g := by
  let x : X := Classical.choice inferInstance
  have hx : row g x ∈ absRowHull g :=
    subset_convexHull ℝ _ (Or.inl ⟨x, rfl⟩)
  have hnx : -row g x ∈ absRowHull g := (absRowHull_symmetric g _).mp hx
  simpa only [smul_neg, add_neg_cancel] using
    (convex_absRowHull g hx hnx (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1))

theorem isCompact_absRowHull [Fintype X] [Fintype Y] : IsCompact (absRowHull g) := by
  exact ((Set.finite_range (row g)).union
    (Set.finite_range (fun x => -row g x))).isCompact_convexHull ℝ

end RowHull

section MatrixBody

variable {X : Type uX} {Y : Type uY} [Fintype Y] (g : Y → X → ℝ) (t : ℝ)

theorem convex_matrixBody : Convex ℝ (matrixBody g t) :=
  ((convex_absRowHull g).smul (3 : ℝ)).add (convex_cube.smul t)

theorem isCompact_matrixBody [Fintype X] : IsCompact (matrixBody g t) :=
  ((isCompact_absRowHull g).smul (3 : ℝ)).add (isCompact_cube.smul t)

omit [Fintype Y] in
theorem matrixBody_symmetric (z : RealSpace Y) :
    z ∈ matrixBody g t ↔ -z ∈ matrixBody g t := by
  have hneg : ∀ w, w ∈ matrixBody g t → -w ∈ matrixBody g t := by
    intro w hw
    rcases Set.mem_add.mp hw with ⟨a, ha, b, hb, rfl⟩
    rcases Set.mem_smul_set.mp ha with ⟨u, hu, rfl⟩
    rcases Set.mem_smul_set.mp hb with ⟨v, hv, rfl⟩
    apply Set.mem_add.mpr
    refine ⟨(3 : ℝ) • (-u),
      Set.smul_mem_smul_set ((absRowHull_symmetric g u).mp hu),
      t • (-v), Set.smul_mem_smul_set ((cube_symmetric v).mp hv), ?_⟩
    simp only [smul_neg, neg_add]
  exact ⟨hneg z, fun hz => by simpa only [neg_neg] using hneg (-z) hz⟩

omit [Fintype Y] in
theorem smul_cube_subset_matrixBody [Nonempty X] : t • cube Y ⊆ matrixBody g t := by
  intro z hz
  apply Set.mem_add.mpr
  refine ⟨0, ?_, z, hz, zero_add z⟩
  simpa only [smul_zero] using
    (Set.smul_mem_smul_set (a := (3 : ℝ)) (zero_mem_absRowHull g))

omit [Fintype Y] in
theorem matrixBody_three_row_mem (x : X) : (3 : ℝ) • row g x ∈ matrixBody g t := by
  apply Set.mem_add.mpr
  refine ⟨(3 : ℝ) • row g x, ?_, 0, ?_, add_zero _⟩
  · exact Set.smul_mem_smul_set (subset_convexHull ℝ _ (Or.inl ⟨x, rfl⟩))
  · simpa only [smul_zero] using
      (Set.smul_mem_smul_set (a := t) (zero_mem_cube (ι := Y)))

theorem zero_mem_interior_matrixBody [Nonempty X] (ht : 0 < t) :
    (0 : RealSpace Y) ∈ interior (matrixBody g t) :=
  interior_mono (smul_cube_subset_matrixBody g t)
    (zero_mem_interior_smul_cube (ne_of_gt ht))

theorem matrixBody_isSymmetricConvexBody [Fintype X] [Nonempty X] (ht : 0 < t) :
    IsSymmetricConvexBody (matrixBody g t) where
  isCompact := isCompact_matrixBody g t
  convex := convex_matrixBody g t
  symmetric := matrixBody_symmetric g t
  interior_nonempty := ⟨0, zero_mem_interior_matrixBody g t ht⟩

end MatrixBody

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.SupportPolar ----
namespace OAI

universe uι uX uY

/-!
# Exact support and polar calculations

Both summands of the matrix body have explicit maximizing points. Consequently
the support equalities below are equalities to attained finite suprema, not
uses of the convention for an empty or unbounded real supremum.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {ι : Type uι} {X : Type uX} {Y : Type uY}

theorem signVector_mem_cube (δ : RealSpace ι) : signVector δ ∈ cube ι := by
  intro i
  simp only [signVector]
  split_ifs <;> norm_num

theorem pairing_signVector [Fintype ι] (δ : RealSpace ι) :
    pairing (signVector δ) δ = l1Norm δ := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ δ i
  · simp [signVector, h, abs_of_nonneg h]
  · simp [signVector, h, abs_of_neg (lt_of_not_ge h)]

theorem pairing_cube_le [Fintype ι] (δ : RealSpace ι) {x : RealSpace ι}
    (hx : x ∈ cube ι) : pairing x δ ≤ l1Norm δ := by
  apply Finset.sum_le_sum
  intro i _
  calc
    x i * δ i ≤ |x i * δ i| := le_abs_self _
    _ = |x i| * |δ i| := abs_mul _ _
    _ ≤ 1 * |δ i| := mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)
    _ = |δ i| := one_mul _

theorem polar_cube [Fintype ι] : polar (cube ι) = l1Ball ι := by
  ext δ
  change (∀ x ∈ cube ι, pairing x δ ≤ 1) ↔ l1Norm δ ≤ 1
  constructor
  · intro h
    rw [← pairing_signVector δ]
    exact h (signVector δ) (signVector_mem_cube δ)
  · intro h x hx
    exact (pairing_cube_le δ hx).trans h

private theorem convex_pairing_le [Fintype ι] (δ : RealSpace ι) (M : ℝ) :
    Convex ℝ {z : RealSpace ι | pairing z δ ≤ M} := by
  intro x hx y hy a b ha hb hab
  change pairing (a • x + b • y) δ ≤ M
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left]
  calc
    a * pairing x δ + b * pairing y δ ≤ a * M + b * M :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = M := by rw [← add_mul, hab, one_mul]

theorem pairing_absRowHull_le_of_bounds [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) {M : ℝ}
    (hM : ∀ x, |pairing (row g x) δ| ≤ M)
    {z : RealSpace Y} (hz : z ∈ absRowHull g) : pairing z δ ≤ M := by
  apply convexHull_min (t := {z : RealSpace Y | pairing z δ ≤ M}) ?_
    (convex_pairing_le δ M) hz
  rintro w (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · exact (abs_le.mp (hM x)).2
  · change pairing (-row g x) δ ≤ M
    rw [pairing_neg_left]
    exact neg_le.mpr (abs_le.mp (hM x)).1

/-- The quantitative pointwise estimate consumed by the polar covering proof. -/
theorem matrixBody_pairing_le_of_bounds [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) {t M L : ℝ} (ht : 0 ≤ t)
    (hM : ∀ x, |pairing (row g x) δ| ≤ M) (hL : l1Norm δ ≤ L)
    {z : RealSpace Y} (hz : z ∈ matrixBody g t) : pairing z δ ≤ 3 * M + t * L := by
  obtain ⟨v0, hv0, w0, hw0, hzEq⟩ := Set.mem_add.mp hz
  obtain ⟨v, hv, hvEq⟩ := Set.mem_smul_set.mp hv0
  obtain ⟨w, hw, hwEq⟩ := Set.mem_smul_set.mp hw0
  rw [← hzEq, ← hvEq, ← hwEq, pairing_add_left, pairing_smul_left, pairing_smul_left]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (pairing_absRowHull_le_of_bounds g δ hM hv) (by norm_num))
    (mul_le_mul_of_nonneg_left ((pairing_cube_le δ hw).trans hL) ht)

theorem mem_smul_polar_matrixBody_of_bounds [Fintype Y]
    (g : Y → X → ℝ) (δ : RealSpace Y) {t M L c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (hM : ∀ x, |pairing (row g x) δ| ≤ M) (hL : l1Norm δ ≤ L)
    (hbound : 3 * M + t * L ≤ c) : δ ∈ c • polar (matrixBody g t) := by
  apply (mem_smul_polar_iff (matrixBody g t) δ hc).mpr
  intro z hz
  exact (matrixBody_pairing_le_of_bounds g δ ht hM hL hz).trans hbound

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.CoveringNumber ----
namespace OAI

universe uι uJ uX

/-!
# Finite covering numbers and the cube packing bound

Centers are arbitrary ambient vectors throughout. Attainment and lower bounds
explicitly assume a finite cover exists, because the natural-number infimum of
the empty set is zero. Compactness and a neighborhood of zero supply that
hypothesis in the geometric application.
-/

noncomputable section

namespace MetricEntropyDuality

open Set Filter
open scoped Topology

variable {ι : Type uι} {A A' B B' : Set (RealSpace ι)}

/-- Every actual finite cover bounds the literal natural infimum. -/
theorem coveringNumber_le_of_covers {M : ℕ} {c : Fin M → RealSpace ι}
    (hc : Covers A B c) : coveringNumber A B ≤ M :=
  Nat.sInf_le ⟨c, hc⟩

theorem coveringNumber_attained (hfin : Coverable A B) :
    ∃ c : Fin (coveringNumber A B) → RealSpace ι, Covers A B c := by
  exact Nat.sInf_mem hfin

/-- The coordinate cube is a neighborhood of zero in a finite product. -/
theorem cube_mem_nhds_zero [Finite ι] : cube ι ∈ 𝓝 (0 : RealSpace ι) := by
  let U : Set (RealSpace ι) := ⋂ i, {x | |x i| < 1}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_abs.comp (continuous_apply i)) continuous_const
  have hzero : (0 : RealSpace ι) ∈ U := by
    simp [U]
  apply Filter.mem_of_superset (hU.mem_nhds hzero)
  intro x hx i
  exact (Set.mem_iInter.mp hx i).le

theorem coverable_cube_of_isCompact [Finite ι] (hA : IsCompact A) :
    Coverable A (cube ι) :=
  coverable_of_isCompact_of_mem_nhds_zero hA cube_mem_nhds_zero

/-- A cube translate has coordinate diameter at most two, for any center. -/
theorem cube_translate_diameter {x y z : RealSpace ι}
    (hx : x - z ∈ cube ι) (hy : y - z ∈ cube ι) (i : ι) :
    |x i - y i| ≤ 2 := by
  have hx' : |x i - z i| ≤ 1 := hx i
  have hy' : |y i - z i| ≤ 1 := hy i
  calc
    |x i - y i| = |(x i - z i) - (y i - z i)| := by congr 1; ring
    _ ≤ |x i - z i| + |y i - z i| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hx' hy'
    _ = 2 := by norm_num

/-- Distinct points separated by more than two cannot share a cube translate. -/
theorem card_le_of_covers_cube {X : Type uX} [Fintype X]
    (p : X → RealSpace ι) (hp : ∀ x, p x ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ i, 2 < |p x i - p y i|)
    {M : ℕ} {c : Fin M → RealSpace ι} (hc : Covers A (cube ι) c) :
    Fintype.card X ≤ M := by
  classical
  choose j hj using fun x => hc (p x) (hp x)
  have hinj : Function.Injective j := by
    intro x y hxy
    by_contra hne
    obtain ⟨i, hi⟩ := hsep x y hne
    have hy : p y - c (j x) ∈ cube ι := by rw [hxy]; exact hj y
    exact (not_lt_of_ge (cube_translate_diameter (hj x) hy i)) hi
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective j hinj

/-- Packing lower bound for the genuine least number of arbitrary translates. -/
theorem card_le_coveringNumber_cube {X : Type uX} [Fintype X]
    (p : X → RealSpace ι) (hp : ∀ x, p x ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ i, 2 < |p x i - p y i|)
    (hfin : Coverable A (cube ι)) :
    Fintype.card X ≤ coveringNumber A (cube ι) := by
  obtain ⟨c, hc⟩ := coveringNumber_attained hfin
  exact card_le_of_covers_cube p hp hsep hc

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.PolarCover ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uX uY

/-!
# Polar covers from arbitrary uniform approximation lists

The functions on the approximation list need not be column combinations.
For every nonempty coefficient fiber we choose an actual vector in the
coefficient ball; empty fibers receive zero. The resulting list has exactly
the original number of slots, with no factor depending on the dimension.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {X : Type uX} {Y : Type uY} [Fintype Y]

/-- The selected coefficient vectors give an actual ambient translate cover
of the whole coefficient ball at the specified polar scale. -/
theorem exists_l1Ball_polar_cover (g : Y → X → ℝ) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 < t) (A : Finset (RealSpace X))
    (hA : UniformApproximation g ε A) :
    ∃ centers : Fin A.card → RealSpace Y,
      (∀ j, centers j ∈ l1Ball Y) ∧
      Covers (l1Ball Y) ((6 * ε + 2 * t) • polar (matrixBody g t)) centers := by
  obtain ⟨centers, hmem, hrep⟩ := exists_coefficient_representatives g ε A hA
  refine ⟨centers, hmem, ?_⟩
  intro lam hLam
  obtain ⟨j, hclose, hnorm⟩ := hrep lam hLam
  refine ⟨j, mem_smul_polar_matrixBody_of_bounds g (lam - centers j)
    ht.le (by linarith) (M := 2 * ε) (L := 2) ?_ hnorm (by linarith)⟩
  intro x
  simpa only [pairing_row_eq_columnCombination, columnCombination_sub, Pi.sub_apply] using
    hclose x

/-- The same explicit finite list covers the literal polar of the cube. -/
theorem exists_cube_polar_cover (g : Y → X → ℝ) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 < t) (A : Finset (RealSpace X))
    (hA : UniformApproximation g ε A) :
    ∃ centers : Fin A.card → RealSpace Y,
      (∀ j, centers j ∈ l1Ball Y) ∧
      Covers (polar (cube Y)) ((6 * ε + 2 * t) • polar (matrixBody g t)) centers := by
  simpa only [polar_cube] using exists_l1Ball_polar_cover g hε ht A hA

/-- Finiteness is supplied by an actual list, independently of the convention
used for an empty natural infimum in the covering-number definition. -/
theorem cube_polar_coverable (g : Y → X → ℝ) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 < t) (A : Finset (RealSpace X))
    (hA : UniformApproximation g ε A) :
    Coverable (polar (cube Y)) ((6 * ε + 2 * t) • polar (matrixBody g t)) := by
  obtain ⟨centers, _, hcover⟩ := exists_cube_polar_cover g hε ht A hA
  exact ⟨A.card, centers, hcover⟩

/-- The least number of arbitrary ambient translates is bounded by the
original approximation-list cardinal, without a dimension or center factor. -/
theorem polar_coveringNumber_le (g : Y → X → ℝ) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 < t) (A : Finset (RealSpace X))
    (hA : UniformApproximation g ε A) :
    coveringNumber (polar (cube Y)) ((6 * ε + 2 * t) • polar (matrixBody g t)) ≤ A.card := by
  obtain ⟨centers, _, hcover⟩ := exists_cube_polar_cover g hε ht A hA
  exact coveringNumber_le_of_covers hcover

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.CoordinateTransport ----
namespace OAI

universe uι uκ

/-!
# Relabelling finite real coordinates

The coordinate map is a linear homeomorphism of the full ambient spaces.
It transports all translation centers, rather than restricting them to the
body being covered. Consequently equality of covering numbers follows from
equality of the sets of admissible natural cover counts.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {ι : Type uι} {κ : Type uκ}

theorem coordinate_image_smul (e : ι ≃ κ) (r : ℝ) (A : Set (ι → ℝ)) :
    coordinateEquiv e '' (r • A) = r • (coordinateEquiv e '' A) :=
  Set.image_smul_comm (coordinateEquiv e) r A ((coordinateEquiv e).map_smul r)

theorem coordinate_isCompact_image (e : ι ≃ κ) (A : Set (ι → ℝ)) :
    IsCompact (coordinateEquiv e '' A) ↔ IsCompact A :=
  (coordinateEquiv e).toHomeomorph.isCompact_image

theorem coordinate_convex_image (e : ι ≃ κ) (A : Set (ι → ℝ)) :
    Convex ℝ (coordinateEquiv e '' A) ↔ Convex ℝ A := by
  constructor
  · intro h
    have hi := h.linear_image (coordinateEquiv e).symm.toLinearEquiv.toLinearMap
    change Convex ℝ ((coordinateEquiv e).symm '' (coordinateEquiv e '' A)) at hi
    simpa only [ContinuousLinearEquiv.symm_image_image] using hi
  · intro h
    exact h.linear_image (coordinateEquiv e).toLinearEquiv.toLinearMap

/-- This is interior in the full ambient function space. -/
theorem coordinate_interior_nonempty (e : ι ≃ κ) (A : Set (ι → ℝ)) :
    (interior (coordinateEquiv e '' A)).Nonempty ↔ (interior A).Nonempty := by
  have hi : coordinateEquiv e '' interior A = interior (coordinateEquiv e '' A) :=
    (coordinateEquiv e).toHomeomorph.image_interior A
  rw [← hi]
  exact Set.image_nonempty

/-- Arbitrary ambient center lists are carried to arbitrary ambient center
lists. No requirement that centers belong to either covered set is added. -/
theorem covers_coordinate_image (e : ι ≃ κ) {M : ℕ}
    (A B : Set (RealSpace ι)) (c : Fin M → RealSpace ι) :
    Covers (coordinateEquiv e '' A) (coordinateEquiv e '' B)
      (fun j => coordinateEquiv e (c j)) ↔ Covers A B c := by
  constructor
  · intro h x hx
    obtain ⟨j, hj⟩ := h (coordinateEquiv e x) ⟨x, hx, rfl⟩
    refine ⟨j, ?_⟩
    have hh := (mem_coordinate_image_iff e B _).mp hj
    simpa only [map_sub, ContinuousLinearEquiv.symm_apply_apply] using hh
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨j, hj⟩ := h x hx
    exact ⟨j, x - c j, hj, map_sub (coordinateEquiv e) x (c j)⟩

theorem exists_cover_coordinate_image (e : ι ≃ κ) (M : ℕ)
    (A B : Set (RealSpace ι)) :
    (∃ c : Fin M → RealSpace κ,
      Covers (coordinateEquiv e '' A) (coordinateEquiv e '' B) c) ↔
      ∃ c : Fin M → RealSpace ι, Covers A B c := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun j => (coordinateEquiv e).symm (c j), ?_⟩
    apply (covers_coordinate_image e A B _).mp
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hc
  · rintro ⟨c, hc⟩
    exact ⟨fun j => coordinateEquiv e (c j),
      (covers_coordinate_image e A B c).mpr hc⟩

theorem coordinate_cover_counts (e : ι ≃ κ) (A B : Set (RealSpace ι)) :
    {M : ℕ | ∃ c : Fin M → RealSpace κ,
      Covers (coordinateEquiv e '' A) (coordinateEquiv e '' B) c} =
      {M : ℕ | ∃ c : Fin M → RealSpace ι, Covers A B c} := by
  ext M
  exact exists_cover_coordinate_image e M A B

theorem coverable_coordinate_image (e : ι ≃ κ) (A B : Set (RealSpace ι)) :
    Coverable (coordinateEquiv e '' A) (coordinateEquiv e '' B) ↔ Coverable A B := by
  unfold Coverable
  exact exists_congr fun M => exists_cover_coordinate_image e M A B

/-- Equality holds even before existence of a finite cover is established:
the two defining sets of natural counts are literally equal. -/
theorem coveringNumber_coordinate_image (e : ι ≃ κ) (A B : Set (RealSpace ι)) :
    coveringNumber (coordinateEquiv e '' A) (coordinateEquiv e '' B) =
      coveringNumber A B := by
  unfold coveringNumber
  rw [coordinate_cover_counts]

theorem coordinate_cube (e : ι ≃ κ) :
    coordinateEquiv e '' cube ι = cube κ := by
  ext y
  rw [mem_coordinate_image_iff]
  change (∀ i, |y (e i)| ≤ 1) ↔ ∀ j, |y j| ≤ 1
  constructor
  · intro h j
    simpa only [e.apply_symm_apply] using h (e.symm j)
  · intro h i
    exact h (e i)

section FiniteCoordinates

variable [Fintype ι] [Fintype κ]

theorem IsSymmetricConvexBody.coordinate_image {K : Set (RealSpace ι)}
    (hK : IsSymmetricConvexBody K) (e : ι ≃ κ) :
    IsSymmetricConvexBody (coordinateEquiv e '' K) where
  isCompact := (coordinate_isCompact_image e K).mpr hK.isCompact
  convex := (coordinate_convex_image e K).mpr hK.convex
  symmetric y := by
    rw [mem_coordinate_image_iff, mem_coordinate_image_iff, map_neg]
    exact hK.symmetric ((coordinateEquiv e).symm y)
  interior_nonempty := (coordinate_interior_nonempty e K).mpr hK.interior_nonempty

theorem coordinate_body_iff (e : ι ≃ κ) (K : Set (RealSpace ι)) :
    IsSymmetricConvexBody (coordinateEquiv e '' K) ↔ IsSymmetricConvexBody K := by
  constructor
  · intro h
    have hh := h.coordinate_image e.symm
    simpa only [← coordinateEquiv_symm, ContinuousLinearEquiv.symm_image_image] using hh
  · exact fun h => h.coordinate_image e

/-- The exact dual covering number in the final theorem is unchanged, for
every scalar, with no convexity or covering premise needed for transport. -/
theorem coveringNumber_polar_cube_coordinate_image (e : ι ≃ κ)
    (K : Set (RealSpace ι)) (a : ℝ) :
    coveringNumber (polar (cube κ)) (a • polar (coordinateEquiv e '' K)) =
      coveringNumber (polar (cube ι)) (a • polar K) := by
  have h := coveringNumber_coordinate_image e (polar (cube ι)) (a • polar K)
  rw [coordinate_polar, coordinate_cube, coordinate_image_smul, coordinate_polar] at h
  exact h

end FiniteCoordinates

theorem coordinate_dimension_pos [Fintype ι] [Nonempty ι] : 0 < Fintype.card ι :=
  Fintype.card_pos

theorem coordinatesToFin_body_iff [Fintype ι] (K : Set (RealSpace ι)) :
    IsSymmetricConvexBody (coordinatesToFin (ι := ι) '' K) ↔
      IsSymmetricConvexBody K :=
  coordinate_body_iff (Fintype.equivFin ι) K

theorem coordinatesToFin_coveringNumber_cube [Fintype ι] (K : Set (RealSpace ι)) :
    coveringNumber (coordinatesToFin (ι := ι) '' K) (cube (Fin (Fintype.card ι))) =
      coveringNumber K (cube ι) := by
  have h := coveringNumber_coordinate_image (Fintype.equivFin ι) K (cube ι)
  rw [coordinate_cube] at h
  exact h

theorem coordinatesToFin_coveringNumber_polar_cube [Fintype ι]
    (K : Set (RealSpace ι)) (a : ℝ) :
    coveringNumber (polar (cube (Fin (Fintype.card ι))))
      (a • polar (coordinatesToFin (ι := ι) '' K)) =
      coveringNumber (polar (cube ι)) (a • polar K) :=
  coveringNumber_polar_cube_coordinate_image (Fintype.equivFin ι) K a

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.MatrixToBody ----
namespace OAI

universe uX uY uι

/-!
# The actual matrix-to-body conversion

The separated points are the actual three-times-scaled rows. The primal
minimum has a finite-cover witness from compactness, and the dual cover has
actual coefficient-ball centers with exactly the approximation-list count.
The final wrapper uses a coordinate linear homeomorphism to obtain `Fin n`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped Pointwise

variable {X : Type uX} {Y : Type uY} [Fintype X] [Fintype Y]

/-- A separated row family supplies the exact primal packing lower bound. -/
theorem matrixBody_primal_lower (g : Y → X → ℝ) (t : ℝ)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|) :
    Fintype.card X ≤ coveringNumber (matrixBody g t) (cube Y) := by
  apply card_le_coveringNumber_cube (fun x => (3 : ℝ) • row g x)
    (matrixBody_three_row_mem g t)
  · intro x x' hne
    obtain ⟨y, hy⟩ := hsep x x' hne
    refine ⟨y, ?_⟩
    change 2 < |3 * g y x - 3 * g y x'|
    rw [← mul_sub, abs_mul]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    linarith
  · exact coverable_cube_of_isCompact (isCompact_matrixBody g t)

/-- Complete geometric conversion for actual real columns. No compactness,
support, polar-cover, or covering-minimum hypothesis is assumed. -/
theorem matrix_to_body [Nonempty X] (g : Y → X → ℝ) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 < t)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace X)) (hA : UniformApproximation g ε A) :
    IsSymmetricConvexBody (matrixBody g t) ∧
      IsSymmetricConvexBody (cube Y) ∧
      Coverable (matrixBody g t) (cube Y) ∧
      Coverable (polar (cube Y)) ((6 * ε + 2 * t) • polar (matrixBody g t)) ∧
      Fintype.card X ≤ coveringNumber (matrixBody g t) (cube Y) ∧
      coveringNumber (polar (cube Y))
        ((6 * ε + 2 * t) • polar (matrixBody g t)) ≤ A.card := by
  exact ⟨matrixBody_isSymmetricConvexBody g t ht, cube_isSymmetricConvexBody,
    coverable_cube_of_isCompact (isCompact_matrixBody g t),
    cube_polar_coverable g hε ht A hA, matrixBody_primal_lower g t hsep,
    polar_coveringNumber_le g hε ht A hA⟩

/-- The actual geometric conversion in the ordinary positive dimension
`card Y`, with all covering centers transported in the same ambient space. -/
theorem matrix_to_body_fin [Nonempty X] [Nonempty Y]
    (g : Y → X → ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace X)) (hA : UniformApproximation g ε A) :
    0 < Fintype.card Y ∧
      ∃ K : Set (RealSpace (Fin (Fintype.card Y))),
        IsSymmetricConvexBody K ∧
        IsSymmetricConvexBody (cube (Fin (Fintype.card Y))) ∧
        Coverable K (cube (Fin (Fintype.card Y))) ∧
        Coverable (polar (cube (Fin (Fintype.card Y)))) ((6 * ε + 2 * t) • polar K) ∧
        Fintype.card X ≤ coveringNumber K (cube (Fin (Fintype.card Y))) ∧
        coveringNumber (polar (cube (Fin (Fintype.card Y))))
          ((6 * ε + 2 * t) • polar K) ≤ A.card := by
  obtain ⟨hK, _, _, hdual, hlo, hhi⟩ := matrix_to_body g hε ht hsep A hA
  let K := coordinatesToFin (ι := Y) '' matrixBody g t
  have hK' : IsSymmetricConvexBody K :=
    (coordinatesToFin_body_iff (matrixBody g t)).mpr hK
  refine ⟨coordinate_dimension_pos, K, hK', cube_isSymmetricConvexBody,
    coverable_cube_of_isCompact hK'.isCompact, ?_, ?_, ?_⟩
  · have htransport := (coverable_coordinate_image (Fintype.equivFin Y)
      (polar (cube Y)) ((6 * ε + 2 * t) • polar (matrixBody g t))).mpr hdual
    rw [coordinate_polar, coordinate_cube, coordinate_image_smul, coordinate_polar]
      at htransport
    exact htransport
  · simpa only [K, coordinatesToFin_coveringNumber_cube] using hlo
  · simpa only [K, coordinatesToFin_coveringNumber_polar_cube] using hhi

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped Pointwise


theorem solution.{uX,uY} : type_of% @_root_.OAI.MetricEntropyDuality.matrix_to_body_fin.{uX,uY} := @_root_.OAI.MetricEntropyDuality.matrix_to_body_fin.{uX,uY}
