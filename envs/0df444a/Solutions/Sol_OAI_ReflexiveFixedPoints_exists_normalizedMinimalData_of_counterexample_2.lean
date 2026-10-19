-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.exists_normalizedMinimalData_of_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:09:47.463271+00:00
-- url     : https://prove2.me/submissions/7efa64f6-c8c9-4a3b-b69e-6d291a36f33a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/Reduction.lean:L27-L49
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.exists_normalizedMinimalData_of_counterexample. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric
import Theorems.Thm_OAI_ReflexiveFixedPoints_exists_minimalInvariantData_of_counterexample
import Theorems.Thm_OAI_ReflexiveFixedPoints_weakCarrier_metrizable

-- ---- from OAI.Analysis.Nonexpansive.WeakCompactness ----
namespace OAI

/-!
# Weak compactness from the actual canonical bidual map

The inverse of the surjective canonical inclusion is weak-star to weak
continuous because its scalar evaluations are precisely the evaluations
of the bidual. Banach–Alaoglu then gives weak compactness of norm balls.
Closed convex subsets are weakly closed by Hahn–Banach separation.
-/

noncomputable section

open Set Metric NormedSpace
open scoped Pointwise

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem differenceBall_eq_inter (K : Set X) :
    differenceBall K = (differenceSpan K : Set X) ∩ closedBall (0 : X) 1 := by
  ext x
  simp only [differenceBall, mem_ofPred_eq, mem_inter_iff, mem_closedBall, dist_zero_right,
    SetLike.mem_coe]

theorem isClosed_differenceBall (K : Set X) : IsClosed (differenceBall K) := by
  rw [differenceBall_eq_inter]
  exact (Submodule.isClosed_topologicalClosure _).inter isClosed_closedBall

theorem isBounded_differenceBall (K : Set X) : Bornology.IsBounded (differenceBall K) := by
  rw [differenceBall_eq_inter]
  exact isBounded_closedBall.subset Set.inter_subset_right

theorem convex_differenceBall (K : Set X) : Convex ℝ (differenceBall K) := by
  rw [differenceBall_eq_inter]
  exact (differenceSpan K).convex.inter (convex_closedBall (0 : X) 1)

/-- Weak compactness of the entire unit ball of the closed difference span. -/
theorem weaklyCompact_differenceBall (hX : CanonicallyReflexive X) (K : Set X) :
    WeaklyCompact (differenceBall K) :=
  weaklyCompact_of_closed_bounded_convex hX (isClosed_differenceBall K)
    (isBounded_differenceBall K) (convex_differenceBall K)

end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.ScalarNormalization ----
namespace OAI

/-!
# Scalar normalization in the original norm

We move the actual invariant set by a positive scalar and conjugate its
map. No norm instance is replaced. Minimality and absence of fixed points
are transported by the explicit inverse scalar multiplication.
-/

noncomputable section

open Set Metric TopologicalSpace
open scoped Pointwise

namespace ReflexiveFixedPoints

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace MinimalInvariantData

/-- Diameter is exactly one after inverse-diameter scaling. -/
theorem scaled_inv_diam (D : MinimalInvariantData (X := X))
    (hX : CanonicallyReflexive X) :
    Metric.diam (D.scaled hX (Metric.diam D.K)⁻¹ (inv_pos.mpr D.diam_pos)).K = 1 := by
  change Metric.diam ((Metric.diam D.K)⁻¹ • D.K) = 1
  rw [diam_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr D.diam_pos),
    inv_mul_cancel₀ D.diam_pos.ne']

end MinimalInvariantData

end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.Reduction ----
namespace OAI

/-!
# Full reduction of an original-norm counterexample

Starting from the given map, this producer constructs the separable minimal
invariant set, scales its points and conjugates its map in the same ambient
space, and proves the weak compactness and metrizability conclusions.
In particular the compact ball is the entire unit ball of the closed
linear span of the differences; compactness of the minimal set alone
would not supply that conclusion.
-/

noncomputable section

open Set TopologicalSpace

namespace ReflexiveFixedPoints

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A genuine original-norm fixed-point-free map produces all normalized
minimal invariant data used by the anchor and switching constructions. -/
theorem exists_normalizedMinimalData_of_counterexample
    (hX : CanonicallyReflexive X) {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C) (hF : LipschitzWith 1 F) (hno : ∀ x : C, F x ≠ x) :
    Nonempty (NormalizedMinimalData (X := X)) := by
  classical
  obtain ⟨D, _hDC⟩ := exists_minimalInvariantData_of_counterexample
    hX hne hclosed hbounded hconvex F hF hno
  let E := D.scaled hX (Metric.diam D.K)⁻¹ (inv_pos.mpr D.diam_pos)
  let : Nonempty E.K := E.nonempty.to_subtype
  let : SeparableSpace E.K := E.separable.separableSpace
  obtain ⟨z, hz⟩ := exists_dense_seq E.K
  exact ⟨{
    toMinimalInvariantData := E
    diam_one := D.scaled_inv_diam hX
    z := z
    dense_z := hz
    weak_metrizable := weakCarrier_metrizable E.separable E.weak_compact
    weak_ball_compact := weaklyCompact_differenceBall hX E.K
  }⟩

end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.exists_normalizedMinimalData_of_counterexample.{u} := @_root_.OAI.ReflexiveFixedPoints.exists_normalizedMinimalData_of_counterexample.{u}
