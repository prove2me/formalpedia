-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.pairNormingFunctional_separates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:56:49.597295+00:00
-- url     : https://prove2.me/submissions/7d0a73fd-ef23-4b83-9eaa-c1c7c193e33c

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric

open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace NormedSpace
open scoped Pointwise
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem solution {K : Set X} (z : ℕ → K)
    (hz : DenseRange z) :
    Function.Injective (fun a : K => fun ij => pairNormingFunctional z ij a) := by
  intro a b hab
  by_contra hne
  have hδ : 0 < ‖(a : X) - b‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hne (Subtype.ext h)
  set δ := ‖(a : X) - b‖
  obtain ⟨i, hi⟩ := hz.exists_dist_lt a (show 0 < δ / 5 by positivity)
  obtain ⟨j, hj⟩ := hz.exists_dist_lt b (show 0 < δ / 5 by positivity)
  rw [Subtype.dist_eq, dist_eq_norm] at hi hj
  have hspec := Classical.choose_spec (exists_dual_vector'' ℝ ((z i : X) - (z j : X)))
  set f := pairNormingFunctional z (i, j)
  have hf1 : ‖f‖ ≤ 1 := hspec.1
  have hf2 : f ((z i : X) - (z j : X)) = ‖(z i : X) - (z j : X)‖ := hspec.2
  have heq : f (a : X) = f (b : X) := congrFun hab (i, j)
  have hdiff : ‖(z i : X) - (z j : X)‖ ≥ 3 * δ / 5 := by
    have : δ ≤ ‖(a : X) - z i‖ + ‖(z i : X) - z j‖ + ‖(z j : X) - b‖ := by
      calc δ = ‖((a : X) - z i) + ((z i : X) - z j) + ((z j : X) - b)‖ := by rw [show ((a : X) - z i) + ((z i : X) - z j) + ((z j : X) - b) = (a : X) - b by abel]
        _ ≤ _ := norm_add₃_le
    have h1 : ‖(z j : X) - b‖ = ‖(b : X) - z j‖ := norm_sub_rev _ _
    linarith
  have herr : |f (((a : X) - z i) - ((b : X) - z j))| ≤ 2 * δ / 5 := by
    have := f.le_opNorm (((a : X) - z i) - ((b : X) - z j))
    have h2 : ‖((a : X) - z i) - ((b : X) - z j)‖ ≤ ‖(a : X) - z i‖ + ‖(b : X) - z j‖ := norm_sub_le _ _
    have h3 : ‖f‖ * ‖((a : X) - z i) - ((b : X) - z j)‖ ≤ 1 * (2 * δ / 5) :=
      mul_le_mul hf1 (by linarith) (norm_nonneg _) zero_le_one
    rw [← Real.norm_eq_abs]; linarith
  have hsplit : f (((a : X) - z i) - ((b : X) - z j)) = -f ((z i : X) - (z j : X)) := by
    have : ((a : X) - z i) - ((b : X) - z j) = ((a : X) - b) - ((z i : X) - z j) := by abel
    rw [this, map_sub, map_sub f (a : X), heq, sub_self, zero_sub]
  rw [hsplit, abs_neg, hf2, abs_of_nonneg (norm_nonneg _)] at herr
  linarith
