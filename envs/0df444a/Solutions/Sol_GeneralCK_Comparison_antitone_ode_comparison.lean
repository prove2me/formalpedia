-- Prove2me | solution 1 for GeneralCK.Comparison.antitone_ode_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:21:59.833097+00:00
-- url     : https://prove2.me/submissions/c4fb8ac4-6d17-4f27-8f75-f69ddbf243f0

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_GeneralCK_Comparison_nonpos_of_deriv_nonpos_when_pos

open scoped BigOperators
namespace GeneralCK.Comparison
end GeneralCK.Comparison

open GeneralCK GeneralCK.Comparison in
open Set in
theorem solution {field u v u' v' : ℝ → ℝ} {s : Set ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hf : AntitoneOn field s)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hdu : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t)
    (hdv : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (v' t) (Ici t) t)
    (hus : ∀ t ∈ Ico 0 T, u t ∈ s) (hvs : ∀ t ∈ Ico 0 T, v t ∈ s)
    (hu' : ∀ t ∈ Ico 0 T, u' t ≤ field (u t))
    (hv' : ∀ t ∈ Ico 0 T, field (v t) ≤ v' t)
    (h0 : u 0 ≤ v 0) : u T ≤ v T := by
  have h := nonpos_of_deriv_nonpos_when_pos hT (hu.sub hv)
    (fun t ht => (hdu t ht).sub (hdv t ht)) (sub_nonpos.mpr h0) (by
      intro t ht hpos
      change 0 < u t - v t at hpos
      have hf' := hf (hvs t ht) (hus t ht) (by linarith)
      have h₁ := hu' t ht
      have h₂ := hv' t ht
      linarith)
  exact sub_nonpos.mp h
