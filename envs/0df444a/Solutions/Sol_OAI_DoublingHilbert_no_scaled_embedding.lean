-- Prove2me | solution 1 for OAI.DoublingHilbert.no_scaled_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:53:38.984651+00:00
-- url     : https://prove2.me/submissions/9f4256bf-92f2-4578-9b54-45b8c47f3217

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Main.lean:L28-L49
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.no_scaled_embedding. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Theorems.Thm_OAI_DoublingHilbert_exists_separated_family
import Theorems.Thm_OAI_DoublingHilbert_isCompact_exists_packing_bound

-- ---- from OAI.Geometry.DoublingHilbert.Main ----
namespace OAI

/-! A doubling Hilbert subset with no finite-dimensional bi-Lipschitz embedding. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open Metric

section Nonembedding
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A normalized finite-dimensional bi-Lipschitz embedding of the fixed set cannot exist. -/
theorem no_normalized_embedding {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (hlower : ∀ p q, dist p q ≤ dist (f p) (f q)) : False := by
  obtain ⟨bound, hbound⟩ := isCompact_exists_packing_bound
    (isCompact_closedBall (0 : E) (D : ℝ)) (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨z, hz, hsep⟩ := exists_separated_family hf hlower (bound + 1) (by omega)
  have hc := hbound z (fun i => by simpa only [mem_closedBall, dist_zero_right] using hz i) hsep
  omega

/-- Arbitrary positive embedding scales reduce to the normalized obstruction. -/
theorem no_scaled_embedding (f : constructedSet → E) {a D : ℝ}
    (ha : 0 < a) (hD : 1 ≤ D)
    (hf : ∀ x y, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ D * a * dist x y) : False := by
  let g : constructedSet → E := fun x => a⁻¹ • f x
  let D' : NNReal := ⟨D, le_trans zero_le_one hD⟩
  have hdist (x y : constructedSet) : dist (g x) (g y) = a⁻¹ * dist (f x) (f y) := by
    simp only [g, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
  have hg : LipschitzWith D' g := LipschitzWith.of_dist_le_mul fun x y => by
    rw [hdist]
    change a⁻¹ * dist (f x) (f y) ≤ D * dist x y
    calc
      _ ≤ a⁻¹ * (D * a * dist x y) :=
        mul_le_mul_of_nonneg_left (hf x y).2 (inv_nonneg.mpr ha.le)
      _ = _ := by field_simp
  apply no_normalized_embedding hg
  intro x y
  rw [hdist]
  calc
    dist x y = a⁻¹ * (a * dist x y) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hf x y).1 (inv_nonneg.mpr ha.le)

end Nonembedding
end DoublingHilbert

namespace DoublingHilbert

end DoublingHilbert

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem solution (f : constructedSet → E) {a D : ℝ}
    (ha : 0 < a) (hD : 1 ≤ D)
    (hf : ∀ x y, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ D * a * dist x y) : False := by
  first
    | exact OAI.DoublingHilbert.no_scaled_embedding f ha hD hf
    | exact OAI.DoublingHilbert.no_scaled_embedding
    | (apply OAI.DoublingHilbert.no_scaled_embedding <;> assumption)
    | (intros; apply OAI.DoublingHilbert.no_scaled_embedding <;> assumption)
