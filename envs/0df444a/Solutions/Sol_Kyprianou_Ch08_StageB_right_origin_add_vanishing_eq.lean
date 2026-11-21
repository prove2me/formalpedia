-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.right_origin_add_vanishing_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:17:24.94989+00:00
-- url     : https://prove2.me/submissions/8ef490ff-b90a-43eb-a192-7e98e6d7daea

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Separation.Hausdorff
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open Filter
open scoped Topology

theorem solution (f g K : ℝ → ℝ) (q : ℝ)
    (hf : Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (f 0)))
    (hg : Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (g 0)))
    (hK : Tendsto K (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ)))
    (heq : ∀ x : ℝ, 0 < x → f x = g x + q * K x) :
    f 0 = g 0 := by
  have hconst : Tendsto (fun _ : ℝ => q) (𝓝[>] (0 : ℝ)) (𝓝 q) :=
    tendsto_const_nhds
  have hsum : Tendsto (fun x => g x + q * K x) (𝓝[>] (0 : ℝ))
      (𝓝 (g 0)) := by
    simpa only [mul_zero, add_zero] using hg.add (hconst.mul hK)
  have hevent : f =ᶠ[𝓝[>] (0 : ℝ)] (fun x => g x + q * K x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    exact heq x hx
  exact tendsto_nhds_unique hf (hsum.congr' hevent.symm)
