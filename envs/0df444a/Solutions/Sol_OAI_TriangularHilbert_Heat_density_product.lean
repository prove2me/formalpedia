-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.density_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:29:16.61648+00:00
-- url     : https://prove2.me/submissions/91d9aced-59b6-4355-9821-be3d261d3c68

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory


theorem solution {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a b p : ℝ) :
    density s (a-p)*density t (b-p) =
      density (s+t) (a-b)*density (s*t/(s+t)) (p-(t*a+s*b)/(s+t)) := by
  have hst : 0 < s + t := by linarith
  have h1 : ∀ a b c d : ℝ, a * Real.exp b * (c * Real.exp d) = (a * c) * Real.exp (b + d) := by
    intros; rw [Real.exp_add]; ring
  unfold density
  rw [h1, h1]
  congr 1
  · rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
  · congr 1
    field_simp
    ring

