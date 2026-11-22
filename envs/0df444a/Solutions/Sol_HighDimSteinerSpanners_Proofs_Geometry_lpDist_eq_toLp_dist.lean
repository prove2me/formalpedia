-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Geometry.lpDist_eq_toLp_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:55.695418+00:00
-- url     : https://prove2.me/submissions/a9aa7148-7edf-450a-ba0d-b832a47965fb

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Geometry
noncomputable section
namespace HighDimSteinerSpanners.Proofs.Geometry
theorem _root_.solution (p : ℝ) (hp : 1 ≤ p) {d : ℕ} (x y : Fin d → ℝ) :
    lpDist p x y =
      dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y) := by
  have hp0 : 0 < p := by linarith
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by positivity
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [PiLp.dist_eq_sum (p := ENNReal.ofReal p) (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
  simp only [ENNReal.toReal_ofReal hp0.le, lpDist, Real.dist_eq, one_div]
end HighDimSteinerSpanners.Proofs.Geometry
