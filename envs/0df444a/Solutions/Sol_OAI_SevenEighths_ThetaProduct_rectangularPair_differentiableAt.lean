-- Prove2me | solution 1 for OAI.SevenEighths.ThetaProduct.rectangularPair_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:19.213352+00:00
-- url     : https://prove2.me/submissions/1efc3511-ee52-47cc-a788-d9a9acc7db0b

import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k

set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.ThetaProduct
namespace OAI.SevenEighths.ThetaProduct
theorem _root_.solution (a b : UnitAddCircle) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (rectangularPair a b u v hu hv).Λ s := by
  exact (rectangularPair a b u v hu hv).differentiableAt_Λ (Or.inl hs₀)
    (Or.inl (by simpa using hs₁))
end OAI.SevenEighths.ThetaProduct
