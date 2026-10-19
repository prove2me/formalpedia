-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.pairNormingFunctional_separates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:06:24.422104+00:00
-- url     : https://prove2.me/submissions/ef931939-72bc-4a3b-baac-817e7f6f6b93

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/WeakMetric.lean:L44-L90
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.pairNormingFunctional_separates. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric

-- ---- from OAI.Analysis.Nonexpansive.WeakMetric ----
namespace OAI

/-!
# Metrizability of norm-separable weakly compact sets

For a dense sequence in the norm carrier, choose a norming functional for
each pairwise difference. These countably many functionals separate the
points of the set. Their evaluations embed the compact weak carrier into
a countable product of real lines. No separability of the ambient space,
or of its entire dual, is assumed.
-/

noncomputable section

open Set TopologicalSpace NormedSpace
open scoped Pointwise

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem pairNormingFunctional_norm {K : Set X} (z : ℕ → K) (ij : ℕ × ℕ) :
    ‖pairNormingFunctional z ij‖ ≤ 1 :=
  (Classical.choose_spec (exists_dual_vector'' ℝ ((z ij.1 : X) - (z ij.2 : X)))).1

theorem pairNormingFunctional_apply {K : Set X} (z : ℕ → K) (ij : ℕ × ℕ) :
    pairNormingFunctional z ij ((z ij.1 : X) - (z ij.2 : X)) =
      ‖(z ij.1 : X) - (z ij.2 : X)‖ :=
  (Classical.choose_spec (exists_dual_vector'' ℝ ((z ij.1 : X) - (z ij.2 : X)))).2

/-- The selected countable family separates the original norm carrier. -/
theorem pairNormingFunctional_separates {K : Set X} (z : ℕ → K)
    (hz : DenseRange z) :
    Function.Injective (fun a : K => fun ij => pairNormingFunctional z ij a) := by
  intro a b hab
  apply Subtype.ext
  by_contra hne
  have hd : 0 < ‖(a : X) - (b : X)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨i, hi⟩ := hz.exists_dist_lt a
    (show 0 < ‖(a : X) - (b : X)‖ / 8 by linarith)
  obtain ⟨j, hj⟩ := hz.exists_dist_lt b
    (show 0 < ‖(a : X) - (b : X)‖ / 8 by linarith)
  have hai : ‖(a : X) - (z i : X)‖ < ‖(a : X) - (b : X)‖ / 8 := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using hi
  have hbj : ‖(b : X) - (z j : X)‖ < ‖(a : X) - (b : X)‖ / 8 := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using hj
  let w : X := (a : X) - (b : X)
  let t : X := (z i : X) - (z j : X)
  let f : StrongDual ℝ X := pairNormingFunctional z (i, j)
  have hf0 : f w = 0 := by
    change f ((a : X) - (b : X)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congr_fun hab (i, j))
  have hft : f t = ‖t‖ := pairNormingFunctional_apply z (i, j)
  have hfn : ‖f‖ ≤ 1 := pairNormingFunctional_norm z (i, j)
  have he : ‖t - w‖ < ‖w‖ / 4 := by
    have heq : t - w = ((z i : X) - (a : X)) - ((z j : X) - (b : X)) := by
      dsimp [t, w]
      abel
    rw [heq]
    have htri := norm_sub_le ((z i : X) - (a : X)) ((z j : X) - (b : X))
    rw [norm_sub_rev (z i : X) (a : X), norm_sub_rev (z j : X) (b : X)] at htri
    dsimp [w]
    linarith
  have ht : ‖t‖ ≤ ‖t - w‖ := calc
    ‖t‖ = f t := hft.symm
    _ = f (t - w) := by rw [map_sub f t w, hf0, sub_zero]
    _ ≤ ‖f (t - w)‖ := le_abs_self _
    _ ≤ ‖f‖ * ‖t - w‖ := f.le_opNorm _
    _ ≤ 1 * ‖t - w‖ := mul_le_mul_of_nonneg_right hfn (norm_nonneg _)
    _ = ‖t - w‖ := one_mul _
  have hw : ‖w‖ ≤ ‖t‖ + ‖t - w‖ := calc
    ‖w‖ = ‖t - (t - w)‖ := by congr 1; abel
    _ ≤ ‖t‖ + ‖t - w‖ := norm_sub_le _ _
  change 0 < ‖w‖ at hd
  linarith

end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace NormedSpace
open scoped Pointwise


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.pairNormingFunctional_separates.{u} := @_root_.OAI.ReflexiveFixedPoints.pairNormingFunctional_separates.{u}
