-- Prove2me | solution 1 for Hirsch.gdist_reach
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:34:49.378984+00:00
-- url     : https://prove2.me/submissions/1133f682-f17e-4c5a-a88f-2c32710356da

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Theorems.Thm_Hirsch_graph_connected_general

open scoped RealInnerProductSpace
set_option autoImplicit false

theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b)) :
    Hirsch.Reach (Hirsch.Hpoly a b) (Hirsch.gdist (Hirsch.Hpoly a b) u v) u v := by
  obtain ⟨L, hw⟩ := Hirsch.graph_connected_general d n a b u v hu hv
  exact Nat.sInf_mem (⟨L, hw⟩ : {k | Hirsch.Reach (Hirsch.Hpoly a b) k u v}.Nonempty)

#print axioms solution
