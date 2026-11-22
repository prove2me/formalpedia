-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.strictMono_partition_tiles
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:45:25.51092+00:00
-- url     : https://prove2.me/submissions/947c27c3-5556-447e-b696-58520d124893

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Refinement of a simple predictable integrand

Refining a `SimplePredictable Ω T` onto a finer partition
(`SimplePredictable.refine`), the pointwise description of the refined
integrand (`SimplePredictable.refine_eval`), and the invariance of the simple
stochastic integral under such a refinement
(`SimplePredictable.simpleIntegral_refine`), obtained by telescoping the driving
increments over each fiber of the refining index map.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]



theorem _root_.solution
    {M : ℕ} {π' : Fin (M + 1) → ℝ} (h_mono : StrictMono π')
    {s : ℝ} (hs_pos : π' 0 < s) (hs_le_last : s ≤ π' (Fin.last M)) :
    ∃ j : Fin M, π' j.castSucc < s ∧ s ≤ π' j.succ := by
  classical
  let Q (k : ℕ) := ∃ i : Fin (M + 1), i.val = k ∧ s ≤ π' i
  have hex : ∃ k, Q k := ⟨M, Fin.last M, rfl, hs_le_last⟩
  obtain ⟨i, hi, hs⟩ := Nat.find_spec hex
  have hip : 0 < i.val := by
    by_contra! hn
    have he : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero hn)
    exact (not_le_of_gt hs_pos) (he ▸ hs)
  let j : Fin M := ⟨i.val - 1, by have := i.isLt; omega⟩
  have hji : j.succ = i := Fin.ext (by change i.val - 1 + 1 = i.val; omega)
  refine ⟨j, ?_, hji.symm ▸ hs⟩
  apply lt_of_not_ge
  intro hj
  have hlt : j.val < Nat.find hex := by change i.val - 1 < Nat.find hex; omega
  exact Nat.find_min hex hlt ⟨j.castSucc, rfl, hj⟩
