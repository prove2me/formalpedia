-- Prove2me | solution 1 for OAI.SevenEighths.ThetaProduct.shiftedPair_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:13.306859+00:00
-- url     : https://prove2.me/submissions/57695a61-f5c2-4bd5-afaa-3f9fe1e44d55

import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct

set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.ThetaProduct
namespace OAI.SevenEighths.ThetaProduct
theorem _root_.solution (a b : UnitAddCircle) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (shiftedPair a b).Λ s := by
  exact (shiftedPair a b).differentiableAt_Λ (Or.inl hs₀)
    (Or.inl (by simpa using hs₁))
end OAI.SevenEighths.ThetaProduct
