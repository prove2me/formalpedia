-- Prove2me | solution 2 for OAI.MetricEntropyDuality.entropyPair_of_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:47:38.610281+00:00
-- url     : https://prove2.me/submissions/f4802e84-aed7-483a-a8cd-d371dc5aa9bc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/MatrixEntropy.lean:L26-L102
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.entropyPair_of_matrix. The node keeps its source
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
import Theorems.Thm_OAI_MetricEntropyDuality_entropy_ratio_bounds
import Theorems.Thm_OAI_MetricEntropyDuality_form_entropy_ratio_le
import Theorems.Thm_OAI_MetricEntropyDuality_matrix_to_body_fin
import Theorems.Thm_OAI_MetricEntropyDuality_mem_smul_polar_iff
import Theorems.Thm_OAI_MetricEntropyDuality_rank_le_formDimension

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

theorem accuracy_cover_scale {a : ℝ} (ha : 1 ≤ a) :
    38 * accuracy a < a⁻¹ := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have heq : 38 * accuracy a = ((38 : ℝ) / 1000) / a := by
    unfold accuracy
    field_simp [ha0.ne']
  rw [heq, ← one_div]
  exact (div_lt_div_iff_of_pos_right ha0).mpr (by norm_num)

theorem compressionRadius_pos (a : ℝ) : 0 < compressionRadius a :=
  Nat.succ_pos _

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.DimensionRatio ----
namespace OAI

/-!
# Exact dimension ratio and rank lower bound

These are identities for the canonical symmetric-form coefficient count.
The ratio is used in the entropy estimate; the lower bound ensures that
the constructed ambient dimensions diverge as the rank increases.
-/

namespace MetricEntropyDuality

/-- A field with at least two elements has more coefficient vectors than
the number of coefficient coordinates. -/
theorem formDimension_le_prime_power {r h p : ℕ} (hp : 2 ≤ p) :
    formDimension r h ≤ p ^ formDimension r h :=
  (show formDimension r h < 2 ^ formDimension r h from Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_left hp _)

theorem rank_le_ambientDimension {r h p n : ℕ} (hr : 0 < r) (hh : 0 < h)
    (hp : 2 ≤ p) (hn : p ^ formDimension r h ≤ n) : r ≤ n :=
  (rank_le_formDimension hr hh).trans ((formDimension_le_prime_power hp).trans hn)

end MetricEntropyDuality

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

theorem coveringNumber_pos (hne : A.Nonempty) (hfin : Coverable A B) :
    0 < coveringNumber A B := by
  obtain ⟨c, hc⟩ := coveringNumber_attained hfin
  obtain ⟨x, hx⟩ := hne
  obtain ⟨j, _⟩ := hc x hx
  exact lt_of_le_of_lt (Nat.zero_le j.val) j.isLt

theorem Covers.mono_right {M : ℕ} {c : Fin M → RealSpace ι}
    (hc : Covers A B c) (hB : B ⊆ B') : Covers A B' c := by
  intro x hx
  obtain ⟨j, hj⟩ := hc x hx
  exact ⟨j, hB hj⟩

theorem Coverable.mono_right (hfin : Coverable A B) (hB : B ⊆ B') :
    Coverable A B' := by
  obtain ⟨M, c, hc⟩ := hfin
  exact ⟨M, c, hc.mono_right hB⟩

theorem coveringNumber_mono_right (hB : B ⊆ B') (hfin : Coverable A B) :
    coveringNumber A B' ≤ coveringNumber A B := by
  obtain ⟨c, hc⟩ := coveringNumber_attained hfin
  exact coveringNumber_le_of_covers (hc.mono_right hB)

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

/-- Increasing a positive polar scale increases the actual covering body. -/
theorem smul_polar_mono {ι : Type uι} [Fintype ι]
    (K : Set (RealSpace ι)) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    c • polar K ⊆ d • polar K := by
  intro δ hδ
  apply (mem_smul_polar_iff K δ (lt_of_lt_of_le hc hcd)).mpr
  intro z hz
  exact le_trans ((mem_smul_polar_iff K δ hc).mp hδ z hz) hcd

/-- The same finite polar cover is valid at every larger positive scale. -/
theorem polar_cover_enlarge {ι : Type uι} [Fintype ι]
    (K : Set (RealSpace ι)) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hfin : Coverable (polar (cube ι)) (c • polar K)) :
    Coverable (polar (cube ι)) (d • polar K) ∧
      coveringNumber (polar (cube ι)) (d • polar K) ≤
        coveringNumber (polar (cube ι)) (c • polar K) := by
  have hsubset := smul_polar_mono K hc hcd
  exact ⟨hfin.mono_right hsubset, coveringNumber_mono_right hsubset hfin⟩

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.PrimeChoice ----
namespace OAI

/-!
# Choosing the prime after the finite parameters

The field size is chosen after the dimension,
direction count, and encoding cost. Infinitude of primes permits all these
bounds to be imposed simultaneously, without any upper bound on the prime.
-/

noncomputable section

namespace MetricEntropyDuality

theorem prime_log_pos {p : ℕ} (hp : p.Prime) : 0 < Real.log (p : ℝ) := by
  apply Real.log_pos
  simpa only [Nat.cast_one] using
    (Nat.cast_lt.mpr hp.one_lt : ((1 : ℕ) : ℝ) < (p : ℝ))

/-- The exponential lower bound on the prime absorbs the fixed encoding cost. -/
theorem prime_choice_entropy_lt {p D : ℕ} (hD : 0 < D)
    {B C : ℝ} (hchoice : Real.exp (B * C / (D : ℝ)) < (p : ℝ)) :
    B * C < (D : ℝ) * Real.log (p : ℝ) := by
  have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hlog := Real.log_lt_log (Real.exp_pos (B * C / (D : ℝ))) hchoice
  rw [Real.log_exp] at hlog
  exact (div_lt_iff₀' hDreal).mp hlog

/-- Positivity of the encoding cost is not needed for this comparison. -/
theorem prime_choice_encoding_ratio_lt {p D : ℕ} (hp : p.Prime) (hD : 0 < D)
    {B C : ℝ} (hB : 0 < B)
    (hchoice : Real.exp (B * C / (D : ℝ)) < (p : ℝ)) :
    2 * C / ((D : ℝ) * Real.log (p : ℝ)) < 2 / B := by
  have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  apply (div_lt_div_iff₀ (mul_pos hDreal (prime_log_pos hp)) hB).mpr
  have hbudget := prime_choice_entropy_lt hD hchoice
  calc
    (2 * C) * B = 2 * (B * C) := by rw [mul_assoc, mul_comm C B]
    _ < 2 * ((D : ℝ) * Real.log (p : ℝ)) :=
      mul_lt_mul_of_pos_left hbudget zero_lt_two

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.MatrixEntropy ----
namespace OAI

universe uX uY

/-!
# Entropy bounds for the actual matrix-to-body output

This intermediate lemma joins the proved geometric conversion to the scalar
entropy estimates. The final construction supplies its literal matrix,
separation and approximation list from the finite-field and compression
theorems; none of these inputs is left as a final endpoint premise.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped Pointwise

/-- Turn an actual separated and compressed matrix into the complete output
record, including finite-cover witnesses and positivity of both cover counts. -/
theorem entropyPair_of_matrix {X : Type uX} {Y : Type uY} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (a : ℝ) (ha : 1 ≤ a) (r : ℕ) (hr : 0 < r)
    (B : ℝ) (hB : 0 < B) (p : ℕ) (hp : p.Prime)
    (hprime : Real.exp (B * encodingCost (compressionRadius a) (accuracy a)
      (directionCount r (compressionRadius a) (accuracy a)) /
        (formDimension r (compressionRadius a) : ℝ)) < (p : ℝ))
    (g : Y → X → ℝ)
    (hrows : Fintype.card X = p ^ formDimension r (compressionRadius a))
    (hcolumns : Fintype.card X ≤ Fintype.card Y)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace X))
    (hA : UniformApproximation g (6 * accuracy a) A)
    (Q : ℕ) (hAQ : A.card ≤ Q ^ 2)
    (hQ : Real.log (Q : ℝ) ≤
      (compressionRadius a : ℝ) * (pivotSlots (accuracy a) : ℝ) *
        Real.log ((p : ℝ) ^ formDimension r (compressionRadius a - 1)) +
          encodingCost (compressionRadius a) (accuracy a)
            (directionCount r (compressionRadius a) (accuracy a))) :
    Nonempty (EntropyPair a r B) := by
  have hθ := accuracy_pos ha
  have hh := compressionRadius_pos a
  have hD := formDimension_pos (j := compressionRadius a) hr
  obtain ⟨hn, K, hK, hcube, hfin, hdualfin, hlo, hhi⟩ :=
    matrix_to_body_fin g (by positivity : 0 ≤ 6 * accuracy a) hθ hsep A hA
  have hscale : 6 * (6 * accuracy a) + 2 * accuracy a = 38 * accuracy a := by ring
  rw [hscale] at hdualfin hhi
  obtain ⟨hdualfin', hmono⟩ := polar_cover_enlarge K
    (by positivity : 0 < 38 * accuracy a) (accuracy_cover_scale ha).le hdualfin
  have hdualpos : 0 < coveringNumber (polar (cube (Fin (Fintype.card Y))))
      (a⁻¹ • polar K) := by
    apply coveringNumber_pos _ hdualfin'
    refine ⟨0, ?_⟩
    intro x hx
    simp
  have hN : p ^ formDimension r (compressionRadius a) ≤
      coveringNumber K (cube (Fin (Fintype.card Y))) := by
    simpa only [hrows] using hlo
  have hm : 1 < p ^ formDimension r (compressionRadius a) :=
    Nat.one_lt_pow (Nat.ne_of_gt hD) hp.one_lt
  have hNpos := hm.trans_le hN
  have hdualQ := hmono.trans (hhi.trans hAQ)
  have hmR : (1 : ℝ) < (p : ℝ) ^ formDimension r (compressionRadius a) := by
    exact_mod_cast hm
  have hNR : (p : ℝ) ^ formDimension r (compressionRadius a) ≤
      (coveringNumber K (cube (Fin (Fintype.card Y))) : ℝ) := by
    exact_mod_cast hN
  have hdualR : (1 : ℝ) ≤
      (coveringNumber (polar (cube (Fin (Fintype.card Y)))) (a⁻¹ • polar K) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hdualpos)
  have hdualQR :
      (coveringNumber (polar (cube (Fin (Fintype.card Y)))) (a⁻¹ • polar K) : ℝ) ≤
        (Q : ℝ) ^ 2 := by exact_mod_cast hdualQ
  have hratios := entropy_ratio_bounds hmR hNR hdualR hdualQR
  have hcompression := form_entropy_ratio_le hr hh hp.one_lt hQ
  have hencoding := prime_choice_encoding_ratio_lt hp hD hB hprime
  have hratiosmall : entropyRatio a K < entropyBudget a r B := by
    apply lt_of_le_of_lt hratios.2
    exact hcompression.trans_lt (add_lt_add_of_le_of_lt (le_refl _) hencoding)
  have hrn : r ≤ Fintype.card Y :=
    rank_le_ambientDimension hr hh hp.two_le (by simpa only [hrows] using hcolumns)
  exact ⟨{
    dimension := Fintype.card Y
    dimension_pos := hn
    rank_le_dimension := hrn
    body := K
    body_isSymmetricConvexBody := hK
    cube_isSymmetricConvexBody := hcube
    primal_coverable := hfin
    dual_coverable := hdualfin'
    primal_one_lt := hNpos
    dual_pos := hdualpos
    primal_log_pos := Real.log_pos (by exact_mod_cast hNpos)
    ratio_nonneg := hratios.1
    ratio_lt := hratiosmall
  }⟩

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped Pointwise


theorem solution.{uX,uY} : type_of% @_root_.OAI.MetricEntropyDuality.entropyPair_of_matrix.{uX,uY} := @_root_.OAI.MetricEntropyDuality.entropyPair_of_matrix.{uX,uY}
