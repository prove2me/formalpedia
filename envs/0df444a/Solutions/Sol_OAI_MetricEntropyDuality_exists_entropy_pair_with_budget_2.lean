-- Prove2me | solution 2 for OAI.MetricEntropyDuality.exists_entropy_pair_with_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:22:40.804368+00:00
-- url     : https://prove2.me/submissions/f8dfd2bb-7e82-4619-9175-b8801e47823c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/Construction.lean:L21-L98
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.exists_entropy_pair_with_budget. The node keeps its source
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
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures
import Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionCode
import Definitions.Def_OAI_Analysis_MetricEntropy_WeightRounding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionDecoder
import Definitions.Def_OAI_Analysis_MetricEntropy_GroupedWeights
import Definitions.Def_OAI_Analysis_MetricEntropy_SignedCompression
import Theorems.Thm_OAI_MetricEntropyDuality_FieldGraphSeparation_no_short_walk
import Theorems.Thm_OAI_MetricEntropyDuality_LogProfile_phi_eq_zero_of_le
import Theorems.Thm_OAI_MetricEntropyDuality_entropyPair_of_matrix
import Theorems.Thm_OAI_MetricEntropyDuality_exists_prime_for_rank
import Theorems.Thm_OAI_MetricEntropyDuality_exists_robust_directions_of_budget
import Theorems.Thm_OAI_MetricEntropyDuality_log_count_le_encodingCost
import Theorems.Thm_OAI_MetricEntropyDuality_uniform_compression

-- ---- from OAI.Analysis.MetricEntropy.FormDimension ----
namespace OAI

universe uK

/-!
# Dimension of symmetric-form coefficients

The coefficients of a symmetric `j`-linear form on an `r`-dimensional space
are indexed by multisets of `j` basis vectors. Their number gives the
dimension of the coefficient space and hence its cardinality over a finite field.
-/

namespace MetricEntropyDuality

/-- Positive ambient dimension gives a nonempty coefficient index set. -/
theorem formDimension_pos {r j : ℕ} (hr : 0 < r) : 0 < formDimension r j := by
  exact Nat.choose_pos (Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_left hr))

/-- Stars and bars counts the actual multiset coefficient indices. -/
theorem card_sym_fin (r j : ℕ) :
    Fintype.card (Sym (Fin r) j) = formDimension r j := by
  simpa only [Fintype.card_fin, formDimension] using
    (Sym.card_sym_eq_choose (α := Fin r) j)

/-- A coefficient function over `ZMod p` has exactly `p` choices at each index. -/
theorem card_form_coefficients (p r j : ℕ) [NeZero p] :
    Fintype.card (Sym (Fin r) j → ZMod p) = p ^ formDimension r j := by
  classical
  rw [Fintype.card_fun, ZMod.card, card_sym_fin]

end MetricEntropyDuality

end OAI

-- ---- from OAI.Analysis.MetricEntropy.Parameters ----
namespace OAI

/-!
# Parameters fixed before the prime is chosen

These are the literal accuracy, pivot-slot, direction-count and encoding-cost
parameters of the construction. The radius and rank are genuinely available
for every proposed comparison constant. Their existence does not depend on
the eventual field size.
-/

noncomputable section

namespace MetricEntropyDuality

theorem accuracy_pos {a : ℝ} (ha : 1 ≤ a) : 0 < accuracy a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  unfold accuracy
  positivity

theorem accuracy_lt_one {a : ℝ} (ha : 1 ≤ a) : accuracy a < 1 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  rw [accuracy, div_lt_one (by positivity : (0 : ℝ) < 1000 * a)]
  linarith

theorem one_div_le_pivotSlots (θ : ℝ) : 1 / θ ≤ (pivotSlots θ : ℝ) :=
  Nat.le_ceil _

theorem pivotSlots_pos {θ : ℝ} (hθ : 0 < θ) : 0 < pivotSlots θ := by
  apply Nat.ceil_pos.mpr
  exact one_div_pos.mpr hθ

theorem one_le_mul_pivotSlots {θ : ℝ} (hθ : 0 < θ) :
    1 ≤ θ * (pivotSlots θ : ℝ) := by
  have hs := (div_le_iff₀ hθ).mp (one_div_le_pivotSlots θ)
  simpa only [mul_comm] using hs

theorem compressionRadius_pos (a : ℝ) : 0 < compressionRadius a :=
  Nat.succ_pos _

theorem compressionRadius_log_pos (a : ℝ) :
    0 < Real.log ((compressionRadius a : ℝ) + 1) := by
  apply Real.log_pos
  have hh : (0 : ℝ) < compressionRadius a := Nat.cast_pos.mpr (compressionRadius_pos a)
  linarith

theorem compressionRadius_log_le {a : ℝ} (ha : 1 ≤ a) :
    Real.log 3 / Real.log ((compressionRadius a : ℝ) + 1) ≤ accuracy a := by
  have hθ := accuracy_pos ha
  have hceil := Nat.le_ceil (Real.exp (Real.log 3 / accuracy a))
  have hbound : Real.exp (Real.log 3 / accuracy a) < (compressionRadius a : ℝ) + 1 := by
    simp only [compressionRadius, Nat.cast_add, Nat.cast_one]
    linarith
  have hlog := Real.log_lt_log (Real.exp_pos (Real.log 3 / accuracy a)) hbound
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ (compressionRadius_log_pos a)).mpr
  have hmul := (div_lt_iff₀ hθ).mp hlog
  nlinarith

theorem directionCount_pos {r h : ℕ} {θ : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hθ : 0 < θ) :
    0 < directionCount r h θ := by
  apply Nat.ceil_pos.mpr
  have hD : (0 : ℝ) < formDimension r h := Nat.cast_pos.mpr (formDimension_pos hr)
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  positivity

/-- The natural ceiling has exactly the direction needed by the deletion argument. -/
theorem directionCount_budget {r h : ℕ} {θ : ℝ} (hθ : 0 < θ) :
    (h : ℝ) * (2 * (formDimension r h : ℝ)) ≤ θ * (directionCount r h θ : ℝ) := by
  have hu : (h : ℝ) * (2 * (formDimension r h : ℝ)) / θ ≤
      (directionCount r h θ : ℝ) := Nat.le_ceil _
  have hmul := (div_le_iff₀ hθ).mp hu
  simpa only [mul_comm] using hmul

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.EntropyBounds ----
namespace OAI

universe uα

/-!
# From finite compression counts to entropy bounds

The counting premise is the literal finite encoding bound. Its logarithmic
conversion and the exact symmetric-form dimension ratio give the scalar
entropy comparison used after the matrix-to-body construction.
-/

noncomputable section

namespace MetricEntropyDuality

/-- Finite-list version retaining the actual nonempty approximating family. -/
theorem log_card_le_encodingCost {α : Type uα} {A : Finset α} {h u q : ℕ} {θ : ℝ}
    (hu : 0 < u) (hq : 0 < q) (hθ : 0 < θ) (hA : A.Nonempty)
    (hcount : (A.card : ℝ) ≤ (u : ℝ) * (q : ℝ) ^ (h * pivotSlots θ) *
      (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ) ^
        (h * pivotSlots θ * 2 ^ u)) :
    Real.log (A.card : ℝ) ≤ (h : ℝ) * (pivotSlots θ : ℝ) * Real.log (q : ℝ) +
      encodingCost h θ u :=
  log_count_le_encodingCost hu hq hθ (Finset.card_pos.mpr hA) hcount

end MetricEntropyDuality

end

end OAI

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

theorem columnCombination_sub [Fintype Y] (g : Y → X → ℝ)
    (lam μ : RealSpace Y) :
    columnCombination g (lam - μ) = columnCombination g lam - columnCombination g μ := by
  funext x
  simp [columnCombination, sub_mul, Finset.sum_sub_distrib]

end Elementary

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.RobustDirections ----
namespace OAI

/-!
# Actual directions surviving deletion

The sample is the full finite product of indexed vectors over `ZMod p`.
The actual symmetric-form count and the zero bound for every repeated-index
tuple feed the disjoint-witness union bound. A finite maximum disjoint family
then produces the surviving set separately for each nonzero form.
-/

noncomputable section

namespace MetricEntropyDuality

/-- The ceiling-defined direction count satisfies the
deletion budget. The field size is chosen after `r`, `h`, and `θ`. -/
theorem exists_robust_directions
    {p r h : ℕ} [Fact p.Prime] (hr : 0 < r) (hh : 0 < h)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp_h : h < p)
    (hp_size : h ^ 2 * (directionCount r h θ) ^ (2 * h) < p) :
    ∃ t : Fin (directionCount r h θ) → Fin r → ZMod p,
      ∀ F : SymmetricForm (ZMod p) r h, F ≠ 0 →
        ∃ T : Finset (Fin (directionCount r h θ)),
          ((Finset.univ \ T).card : ℝ) ≤ θ * (directionCount r h θ : ℝ) ∧
            T.Nonempty ∧
          ∀ a : Fin h → Fin (directionCount r h θ), (∀ j, a j ∈ T) →
            SymmetricForm.eval F (fun j => t (a j)) ≠ 0 :=
  exists_robust_directions_of_budget hr hh (directionCount_pos hr hh hθ0)
    hθ1 (directionCount_budget hθ0) hp_h hp_size

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.PartitionGraph ----
namespace OAI

universe uX uι uLabel

/-!
# Partition graphs and their extended distances

An edge records equality of one selected label. Distances take values in `ℕ∞`,
so vertices in different connected components have infinite distance. The
pivot comparison and finite-walk characterization control the paths
between vertices with common labels.
-/

noncomputable section

namespace MetricEntropyDuality.PartitionGraph

variable {X : Type uX} {ι : Type uι} {Label : ι → Type uLabel}
variable (L : (i : ι) → X → Label i) (T : Finset ι)

theorem distance_comm (x y : X) : distance L T x y = distance L T y x :=
  SimpleGraph.edist_comm

/-- Every finite distance bound is witnessed by an actual walk. -/
theorem exists_walk_of_le {k : ℕ} {x y : X}
    (h : distance L T x y ≤ (k : ℕ∞)) :
    ∃ p : (graph L T).Walk x y, p.length ≤ k := by
  have htop : (graph L T).edist x y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
  exact ⟨p, ENat.natCast_le_natCast.mp (hp.trans_le h)⟩

/-- To separate vertices beyond radius `k`, it suffices to rule out short walks. -/
theorem lt_distance_of_forall_walk {k : ℕ} {x y : X}
    (h : ∀ p : (graph L T).Walk x y, k < p.length) :
    (k : ℕ∞) < distance L T x y := by
  apply lt_of_not_ge
  intro hle
  obtain ⟨p, hp⟩ := exists_walk_of_le L T hle
  exact (Nat.not_lt_of_ge hp) (h p)

end MetricEntropyDuality.PartitionGraph

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.FieldGraphSeparation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uK uι uα uV uA

/-!
# Actual contraction labels obstruct short walks

One label is chosen for each edge of a hypothetical short walk. These labels
are padded to the full degree using one fixed member of the same set of
directions. Symmetry moves each edge's direction to the contracted slot, so
evaluation on this single tuple is constant along the walk. This contradicts
robust nonvanishing of the difference of its endpoints.
-/

noncomputable section

namespace MetricEntropyDuality

namespace SymmetricForm

variable {K : Type uK} [CommSemiring K] {r j : ℕ}

end SymmetricForm

namespace FieldGraphSeparation

variable {K : Type uK} {ι : Type uι} [CommRing K] {r j : ℕ}

/-- Separation in the extended graph metric, including disconnected endpoints. -/
theorem distance_gt (t : ι → (Fin r → K)) (T : Finset ι) (hT : T.Nonempty)
    (x y : SymmetricForm K r (j + 1))
    (hrobust : ∀ a : Fin (j + 1) → ι, (∀ l, a l ∈ T) →
      (y - x).eval (fun l => t (a l)) ≠ 0) :
    ((j + 1 : ℕ) : ℕ∞) < PartitionGraph.distance (labels t) T x y := by
  exact PartitionGraph.lt_distance_of_forall_walk (labels t) T
    (no_short_walk t T hT x y hrobust)

end FieldGraphSeparation
end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.GraphProfile ----
namespace OAI

universe uX uι uLabel

/-!
# The actual logarithmic graph matrix

Columns retain both their vertex and their admissible partition set. The graph
metric takes values in ENat, so disconnected vertices have profile zero.
The row separation proof uses an actual coordinate of this matrix; the finite
field construction supplies its graph-separation hypothesis separately.
-/

noncomputable section

namespace MetricEntropyDuality.GraphProfile

open scoped BigOperators

variable {X : Type uX} {ι : Type uι} {Label : ι → Type uLabel}

theorem column_self (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (_hh : 0 < h) (x : X) (T : {T : Finset ι // T ∈ 𝒯}) :
    column L 𝒯 h (x, T) x = 1 := by
  unfold column
  rw [PartitionGraph.distance_self]
  exact LogProfile.phi_zero h

theorem column_eq_zero_of_le (L : (i : ι) → X → Label i)
    (𝒯 : Finset (Finset ι)) {h : ℕ} (hh : 0 < h)
    (y : Columns X 𝒯) (x : X)
    (hd : (h : ℕ∞) ≤ PartitionGraph.distance L y.2.val x y.1) :
    column L 𝒯 h y x = 0 :=
  LogProfile.phi_eq_zero_of_le hh hd

/-- The concrete coordinate witness consumed by the convex-body construction. -/
theorem exists_column_abs_eq_one (L : (i : ι) → X → Label i)
    (𝒯 : Finset (Finset ι)) {h : ℕ} (hh : 0 < h) (x z : X)
    (hsep : ∃ T ∈ 𝒯, (h : ℕ∞) < PartitionGraph.distance L T x z) :
    ∃ y : Columns X 𝒯, |column L 𝒯 h y x - column L 𝒯 h y z| = 1 := by
  obtain ⟨T, hT, hd⟩ := hsep
  let c : Columns X 𝒯 := (x, ⟨T, hT⟩)
  have hx : column L 𝒯 h c x = 1 := column_self L 𝒯 hh x ⟨T, hT⟩
  have hz : column L 𝒯 h c z = 0 := by
    apply column_eq_zero_of_le L 𝒯 hh c z
    change (h : ℕ∞) ≤ PartitionGraph.distance L T z x
    rw [PartitionGraph.distance_comm]
    exact hd.le
  refine ⟨c, ?_⟩
  rw [hx, hz, sub_zero, abs_one]

end MetricEntropyDuality.GraphProfile

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.FiniteFieldRows ----
namespace OAI

/-!
# The finite-field graph matrix

The rows are literal symmetric forms, the labels are their actual contractions,
and every admissible set is included as a column index. The only input to the
separation theorem is the repeated-tuple nonvanishing conclusion constructed
by the robust-directions argument; graph separation is proved from it.
-/

noncomputable section

namespace MetricEntropyDuality.FiniteFieldRows

theorem full_mem_admissibleSets {θ : ℝ} (hθ : 0 ≤ θ) (u : ℕ) :
    Finset.univ ∈ admissibleSets θ u := by
  apply mem_admissibleSets.mpr
  simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
  exact mul_nonneg hθ (Nat.cast_nonneg u)

theorem card_rowIndex (p r h : ℕ) [NeZero p] :
    Fintype.card (RowIndex p r h) = p ^ formDimension r h :=
  card_form_coefficients p r h

/-- Including the full index set gives at least one column per row. -/
theorem card_rowIndex_le_columns {θ : ℝ} (hθ : 0 ≤ θ)
    (p r h u : ℕ) [NeZero p] :
    Fintype.card (RowIndex p r h) ≤ Fintype.card (ColumnIndex θ p r h u) := by
  classical
  apply Fintype.card_le_of_injective
    (fun x : RowIndex p r h => (x, ⟨Finset.univ, full_mem_admissibleSets hθ u⟩))
  intro x z hxz
  exact congrArg Prod.fst hxz

theorem columnIndex_nonempty {θ : ℝ} (hθ : 0 ≤ θ) (p r h u : ℕ) :
    Nonempty (ColumnIndex θ p r h u) :=
  ⟨(0, ⟨Finset.univ, full_mem_admissibleSets hθ u⟩)⟩

section Separation

variable {p r j u : ℕ} [NeZero p] {θ : ℝ}
variable (t : Fin u → (Fin r → ZMod p))
variable (hrobust : ∀ Z : SymmetricForm (ZMod p) r (j + 1), Z ≠ 0 →
  ∃ T : Finset (Fin u), ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) ∧
    T.Nonempty ∧ ∀ a : Fin (j + 1) → Fin u, (∀ l, a l ∈ T) →
      Z.eval (fun l => t (a l)) ≠ 0)

include hrobust

omit [NeZero p] in
/-- Robust nonvanishing gives separation in one of the actual admissible graphs. -/
theorem graph_separation (x y : RowIndex p r (j + 1)) (hxy : x ≠ y) :
    ∃ T ∈ admissibleSets θ u,
      ((j + 1 : ℕ) : ℕ∞) < PartitionGraph.distance (labels t) T x y := by
  obtain ⟨T, hbound, hT, hnonzero⟩ := hrobust (y - x) (sub_ne_zero.mpr hxy.symm)
  exact ⟨T, mem_admissibleSets.mpr hbound,
    FieldGraphSeparation.distance_gt t T hT x y hnonzero⟩

omit [NeZero p] in
/-- This coordinate statement is the direct input to the convex-body argument. -/
theorem exists_column_abs_eq_one (x y : RowIndex p r (j + 1)) (hxy : x ≠ y) :
    ∃ c : ColumnIndex θ p r (j + 1) u,
      |column θ t c x - column θ t c y| = 1 :=
  GraphProfile.exists_column_abs_eq_one (labels t) (admissibleSets θ u)
    (Nat.succ_pos j) x y (graph_separation t hrobust x y hxy)

end Separation
end MetricEntropyDuality.FiniteFieldRows

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.SignedCompression ----
namespace OAI

universe uX uY

/-!
# Signed compression and actual coefficient-ball clusters

A common finite approximation list for nonnegative combinations of mass at
most one gives a difference list for the literal `l1Ball`. A chosen pair of
positive approximants labels each actual coefficient vector; equal labels
give a uniform diameter bound. The list may have centers outside the column
hull, while the fibers consist of actual coefficient vectors.
-/

noncomputable section

namespace MetricEntropyDuality.SignedCompression

open scoped BigOperators

variable {X : Type uX} {Y : Type uY} [Fintype Y]

omit [Fintype Y] in
theorem positivePart_nonneg (lam : RealSpace Y) (y : Y) :
    0 ≤ positivePart lam y := le_max_right _ _

omit [Fintype Y] in
theorem negativePart_nonneg (lam : RealSpace Y) (y : Y) :
    0 ≤ negativePart lam y := le_max_right _ _

omit [Fintype Y] in
theorem parts_sub (lam : RealSpace Y) : positivePart lam - negativePart lam = lam := by
  funext y
  change max (lam y) 0 - max (-lam y) 0 = lam y
  by_cases h : 0 ≤ lam y
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · have hle : lam y ≤ 0 := le_of_lt (lt_of_not_ge h)
    simp [max_eq_right hle, max_eq_left (neg_nonneg.mpr hle)]

theorem sum_positivePart_le_one (lam : RealSpace Y) (hlam : lam ∈ l1Ball Y) :
    ∑ y, positivePart lam y ≤ 1 := by
  calc
    ∑ y, positivePart lam y ≤ l1Norm lam := by
      apply Finset.sum_le_sum
      intro y _
      exact max_le (le_abs_self (lam y)) (abs_nonneg (lam y))
    _ ≤ 1 := hlam

theorem sum_negativePart_le_one (lam : RealSpace Y) (hlam : lam ∈ l1Ball Y) :
    ∑ y, negativePart lam y ≤ 1 := by
  calc
    ∑ y, negativePart lam y ≤ l1Norm lam := by
      apply Finset.sum_le_sum
      intro y _
      exact max_le (neg_le_abs (lam y)) (abs_nonneg (lam y))
    _ ≤ 1 := hlam

theorem sub_close {ε η : ℝ} {f f' a a' : RealSpace X}
    (hf : UniformClose ε f a) (hf' : UniformClose η f' a') :
    UniformClose (ε + η) (f - f') (a - a') := by
  intro x
  change |(f x - f' x) - (a x - a' x)| ≤ ε + η
  calc
    |(f x - f' x) - (a x - a' x)| = |(f x - a x) - (f' x - a' x)| := by
      congr 1
      ring
    _ ≤ |f x - a x| + |f' x - a' x| := abs_sub _ _
    _ ≤ ε + η := add_le_add (hf x) (hf' x)

theorem differenceList_card_le (A : Finset (RealSpace X)) :
    (differenceList A).card ≤ A.card ^ 2 := by
  classical
  calc
    (differenceList A).card ≤ (A.product A).card := Finset.card_image_le
    _ = A.card ^ 2 := by rw [Finset.product_eq_sprod, Finset.card_product, pow_two]

theorem decode_mem_differenceList {A : Finset (RealSpace X)} (c : Code A) :
    decode c ∈ differenceList A := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(c.1.val, c.2.val), Finset.mem_product.mpr ⟨c.1.property, c.2.property⟩, rfl⟩

variable (g : Y → X → ℝ) (θ : ℝ) (A : Finset (RealSpace X))

theorem exists_code_approximation (hpos : PositiveApproximation g θ A)
    (lam : RealSpace Y) (hlam : lam ∈ l1Ball Y) :
    ∃ c : Code A, UniformClose (6 * θ) (columnCombination g lam) (decode c) := by
  obtain ⟨a, ha, hapos⟩ := hpos (positivePart lam) (positivePart_nonneg lam)
    (sum_positivePart_le_one lam hlam)
  obtain ⟨b, hb, haneg⟩ := hpos (negativePart lam) (negativePart_nonneg lam)
    (sum_negativePart_le_one lam hlam)
  refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
  change UniformClose (6 * θ) (columnCombination g lam) (a - b)
  have h := sub_close hapos haneg
  rw [← columnCombination_sub, parts_sub] at h
  have hsum : 3 * θ + 3 * θ = 6 * θ := by ring
  simpa only [hsum] using h

/-- Signed combinations are approximated by the actual finite difference list. -/
theorem uniformApproximation (hpos : PositiveApproximation g θ A) :
    UniformApproximation g (6 * θ) (differenceList A) := by
  intro lam hlam
  obtain ⟨c, hc⟩ := exists_code_approximation g θ A hpos lam hlam
  exact ⟨decode c, decode_mem_differenceList c, hc⟩

end MetricEntropyDuality.SignedCompression

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.Construction ----
namespace OAI

/-!
# The unconditional construction with the prime chosen last

The only inputs are the proposed scale, a positive rank, and a positive
entropy budget. The prime, robust directions, contraction partitions,
separated real matrix, positive and signed approximation lists, and actual
convex body are all constructed by the preceding theorems.
-/

noncomputable section

namespace MetricEntropyDuality

/-- Construct actual full-dimensional bodies and their strict entropy bound.
There is no matrix, compression, geometric, or entropy premise. -/
theorem exists_entropy_pair_with_budget (a : ℝ) (ha : 1 ≤ a)
    (r : ℕ) (hr : 1 ≤ r) (B : ℝ) (hB : 0 < B) :
    Nonempty (EntropyPair a r B) := by
  classical
  have hr₀ : 0 < r := hr
  let θ := accuracy a
  let h := compressionRadius a
  let j := h - 1
  have hh : 0 < h := compressionRadius_pos a
  have hj : j + 1 = h := Nat.sub_add_cancel hh
  have hθ : 0 < θ := accuracy_pos ha
  have hθ₁ : θ < 1 := accuracy_lt_one ha
  -- The preceding real and finite quantities are fixed before `p` is selected.
  obtain ⟨p, hp, _, hp_h, hp_size, hp_entropy, _, _, _, _⟩ :=
    exists_prime_for_rank ha hr₀ B 0 hB
  let : Fact p.Prime := ⟨hp⟩
  let u := directionCount r (j + 1) θ
  have hu : 0 < u := directionCount_pos hr₀ (Nat.succ_pos j) hθ
  have hp_h' : j + 1 < p := by simpa only [hj] using hp_h
  have hp_size' : (j + 1) ^ 2 * u ^ (2 * (j + 1)) < p := by
    simpa only [u, hj] using hp_size
  obtain ⟨t, hrobust⟩ := exists_robust_directions
    hr₀ (Nat.succ_pos j) hθ hθ₁ hp_h' hp_size'
  let X := FiniteFieldRows.RowIndex p r (j + 1)
  let Y := FiniteFieldRows.ColumnIndex θ p r (j + 1) u
  let : Nonempty X := ⟨0⟩
  let : Nonempty Y := FiniteFieldRows.columnIndex_nonempty hθ.le p r (j + 1) u
  let L := FiniteFieldRows.labels (j := j) t
  let 𝒯 := FiniteFieldRows.admissibleSets θ u
  let g : Y → X → ℝ := FiniteFieldRows.column (j := j) θ t
  let q := p ^ formDimension r j
  have hq : 0 < q := pow_pos hp.pos _
  have hlabels : ∀ i, Nat.card (Set.range (L i)) ≤ q := by
    intro i
    calc
      Nat.card (Set.range (L i)) ≤ Nat.card (SymmetricForm (ZMod p) r j) :=
        Nat.card_le_card_of_injective (fun z : Set.range (L i) => z.val)
          Subtype.val_injective
      _ = q := by rw [Nat.card_eq_fintype_card, card_form_coefficients]
  have hcomp : ∀ T ∈ 𝒯, ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) := by
    intro T hT
    exact FiniteFieldRows.mem_admissibleSets.mp hT
  have hsθ : 1 ≤ (pivotSlots θ : ℝ) * θ := by
    simpa only [mul_comm] using one_le_mul_pivotSlots hθ
  have hprofile : Real.log 3 / Real.log (((j + 1 : ℕ) : ℝ) + 1) ≤ θ := by
    simpa only [hj] using compressionRadius_log_le ha
  obtain ⟨A, hAne, hcount, hpositive⟩ := uniform_compression
    (L := L) (hlabels := hlabels) (𝒯 := 𝒯) (hu := hu) (hq := hq)
    (hh := Nat.succ_pos j) (hs := pivotSlots_pos hθ) (θ := θ) (hθ := hθ)
    (hsθ := hsθ) (hprofile := hprofile) (hcomp := hcomp)
  have hsigned : UniformApproximation g (6 * θ)
      (SignedCompression.differenceList A) :=
    SignedCompression.uniformApproximation g θ A hpositive
  have hlog := log_card_le_encodingCost hu hq hθ hAne hcount
  have hlog' : Real.log (A.card : ℝ) ≤
      (compressionRadius a : ℝ) * (pivotSlots (accuracy a) : ℝ) *
        Real.log ((p : ℝ) ^ formDimension r (compressionRadius a - 1)) +
          encodingCost (compressionRadius a) (accuracy a)
            (directionCount r (compressionRadius a) (accuracy a)) := by
    change Real.log (A.card : ℝ) ≤
      (h : ℝ) * (pivotSlots θ : ℝ) * Real.log ((p : ℝ) ^ formDimension r j) +
        encodingCost h θ (directionCount r h θ)
    simpa only [q, Nat.cast_pow, u, Nat.succ_eq_add_one, hj] using hlog
  have hrows : Fintype.card X = p ^ formDimension r (compressionRadius a) := by
    change Fintype.card (FiniteFieldRows.RowIndex p r (j + 1)) =
      p ^ formDimension r h
    simpa only [hj] using FiniteFieldRows.card_rowIndex p r (j + 1)
  have hcolumns : Fintype.card X ≤ Fintype.card Y :=
    FiniteFieldRows.card_rowIndex_le_columns hθ.le p r (j + 1) u
  have hsep : ∀ x x' : X, x ≠ x' → ∃ y : Y, 1 ≤ |g y x - g y x'| := by
    intro x x' hxx'
    obtain ⟨y, hy⟩ := FiniteFieldRows.exists_column_abs_eq_one t hrobust x x' hxx'
    exact ⟨y, hy.ge⟩
  exact entropyPair_of_matrix a ha r hr₀ B hB p hp hp_entropy g
    hrows hcolumns hsep (SignedCompression.differenceList A) hsigned
    A.card (SignedCompression.differenceList_card_le A) hlog'

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.exists_entropy_pair_with_budget := @_root_.OAI.MetricEntropyDuality.exists_entropy_pair_with_budget
