-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteEntropy.entropy_ge_neg_log_of_density
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:42:39.531341+00:00
-- url     : https://prove2.me/submissions/c1b94205-4073-43e5-a879-ac40bb63a719

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean:L132-L146
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteEntropy.entropy_ge_neg_log_of_density. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy

-- ---- from OAI.Combinatorics.CliqueFree.FiniteEntropy ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteEntropy

variable {I : Type u} [Fintype I]

lemma entropy_ge_neg_log_of_density {w p : I → ℝ} (_hw : ∀ i, 0 < w i)
    (hp : IsProb p) {b : ℝ} (hb : 0 < b) (hden : ∀ i, p i ≤ b * w i) :
    -Real.log b ≤ entropy w p := by
  have hi (i : I) : p i * (-Real.log b) ≤ p i * Real.log (w i / p i) := by
    rcases (hp.1 i).eq_or_lt with hi | hi
    · simp [← hi]
    apply mul_le_mul_of_nonneg_left _ hi.le
    rw [← Real.log_inv]
    apply Real.log_le_log (inv_pos.2 hb)
    apply (le_div_iff₀ hi).2
    calc
      b⁻¹ * p i = p i / b := by ring
      _ ≤ w i := (div_le_iff₀ hb).2 (by simpa [mul_comm] using hden i)
  have h := sum_le_sum (s := univ) fun i _ ↦ hi i
  simpa [← sum_mul, hp.2, entropy] using h

variable {J : Type v} [Fintype J]

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteEntropy
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteEntropy.entropy_ge_neg_log_of_density.{u} := @_root_.OAI.CliqueFreeIndependence.FiniteEntropy.entropy_ge_neg_log_of_density.{u}
