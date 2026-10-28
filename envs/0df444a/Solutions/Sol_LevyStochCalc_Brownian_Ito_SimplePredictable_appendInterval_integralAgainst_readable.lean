-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.appendInterval_integralAgainst_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:01.618596+00:00
-- url     : https://prove2.me/submissions/f1fb184c-3412-494a-bacc-c01c1baeb854

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The zero-extension leaves the elementary integral against a process unchanged. -/
theorem solution
    {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T) {T' : ℝ}
    (hlt : G.partition (Fin.last G.N) < T') (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (G.appendInterval hlt).integralAgainst M t ω = G.integralAgainst M t ω := by
  unfold LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst
  rw [G.appendInterval_partition_eq hlt, G.appendInterval_xi_eq hlt]
  change (∑ i : Fin (G.N + 1),
      (Fin.snoc (α := fun _ => Ω → ℝ) G.ξ (fun _ : Ω => (0 : ℝ))) i ω
        * (M (min ((Fin.snoc (α := fun _ => ℝ) G.partition T') i.succ) t) ω
            - M (min ((Fin.snoc (α := fun _ => ℝ) G.partition T') i.castSucc) t) ω))
    = ∑ i : Fin G.N, G.ξ i ω
        * (M (min (G.partition i.succ) t) ω - M (min (G.partition i.castSucc) t) ω)
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Fin.castSucc i).succ = Fin.castSucc i.succ from Fin.ext rfl]
  simp only [Fin.snoc_castSucc]
