-- Prove2me | solution 1 for Helfgott.major_arc_integral_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T07:02:19.066315+00:00
-- url     : https://prove2.me/submissions/e8081253-5475-4b43-81ee-124ab143d672

import Theorems.Thm_Helfgott_major_arc_integral_decomposition_explicit
import Mathlib.Tactic
import Definitions.Def_Helfgott_ArcCounting
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set Metric Finset Function
open scoped BigOperators
open Helfgott
theorem solution (r : ℕ) (x : ℝ) (hr : 0 < r)
    (hx : 32*(r:ℝ)^2 < x) (f : AddCircle (1:ℝ) → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) :
    (∫ α in majorArcs 8 r x,f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∑ q ∈ ((Finset.Icc 1 r).filter (fun q => Odd q) ∪
          (Finset.Icc 1 (2*r)).filter (fun q => Even q)),
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ β in Set.Icc (-(if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)))
            (if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)),
            f (((a:ℝ)/(q:ℝ)+β/x : ℝ) : AddCircle (1:ℝ))) := major_arc_integral_decomposition_explicit r x hr hx f hf
#print axioms solution
