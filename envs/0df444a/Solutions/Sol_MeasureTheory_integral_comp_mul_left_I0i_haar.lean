-- Prove2me | solution 1 for MeasureTheory.integral_comp_mul_left_I0i_haar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T18:13:17.900008+00:00
-- url     : https://prove2.me/submissions/abb6c25b-0e61-43d6-b7f5-60ffd4e06fb7

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_MellinCalculus_defs
import Theorems.Thm_MeasureTheory_integral_comp_mul_right_I0i_haar

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

open MeasureTheory in
theorem solution
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a * y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  convert integral_comp_mul_right_I0i_haar f ha using 5; ring

-- TODO: generalize to `RCLike`

local notation (name := mellintransform) "𝓜" => mellin

-- filter-free version:

-- This lemma might not be necessary, but the RHS is supported on [0, infinity), which makes
-- results like `support_MellinConvolution_subsets` easier to apply.

/-% ** Wrong delimiters on purpose, no need to include this in the LaTeX outline
\begin{lemma}[Smooth1Properties_estimate]\label{Smooth1Properties_estimate}
\lean{Smooth1Properties_estimate}\leanok
For $\epsilon>0$,
$$
  \log2>\frac{1-2^{-\epsilon}}\epsilon
$$
\end{lemma}
%-/
