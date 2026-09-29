-- Prove2me | solution 3 for Mandelbrot.mandelbrot_isConnected
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-24T21:20:53.177782+00:00
-- url     : https://prove2.me/submissions/aa9cbdf5-d8e9-478c-9072-d2765db42a3f

import Definitions.Def_mandelbrot_sets
import Definitions.Def_ray_multibrot_connected

/-!
# The Mandelbrot set is connected (Douady–Hubbard)

The analytic work is done in Geoffrey Irving's formalization *ray*
(https://github.com/girving/ray, Apache License 2.0), published on the platform as the chain of
definition files `ray_analytic_basics`, …, `ray_multibrot_connected`. The last of these provides
`isConnected_mandelbrot : IsConnected mandelbrot`, where ray's
`mandelbrot = {c | ¬Tendsto (fun n ↦ ‖(fun z ↦ z^2 + c)^[n] c‖) atTop atTop}`.
Here we identify ray's set with the platform's `Mandelbrot.mandelbrotSet` and conclude.
-/

/-- The platform's Mandelbrot set coincides with ray's `mandelbrot`: the orbit of `0` escapes in
the cobounded filter iff the norms of the orbit of `c = f_c(0)` tend to `∞`. -/
theorem Mandelbrot.mandelbrotSet_eq_ray_mandelbrot : Mandelbrot.mandelbrotSet = mandelbrot := by
  ext c
  simp only [Mandelbrot.mandelbrotSet, Mandelbrot.multibrotSet, mandelbrot, Set.mem_ofPred_eq]
  have e : (fun n : ℕ ↦ ‖(fun z : ℂ ↦ z ^ 2 + c)^[n] c‖) =
      (fun k : ℕ ↦ ‖(fun z : ℂ ↦ z ^ 2 + c)^[k] 0‖) ∘ (fun n ↦ n + 1) := by
    funext n
    simp [Function.iterate_succ_apply]
  rw [e, ← tendsto_norm_atTop_iff_cobounded, ← Filter.tendsto_add_atTop_iff_nat 1]
  rfl

theorem solution : IsConnected Mandelbrot.mandelbrotSet := by
  rw [Mandelbrot.mandelbrotSet_eq_ray_mandelbrot]
  exact isConnected_mandelbrot
