-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.thetaExp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:23.571662+00:00
-- url     : https://prove2.me/submissions/fd80855e-fe34-41cc-809b-7bc17c80cbba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped Real ContDiff
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) (l l' : Fl g)
    (z : Fin g → ℂ) :
    thetaExp τ (l + l') z = thetaExp τ l (z + per τ l') + thetaExp τ l' z +
      ∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ) := by
  set p : Fin g → ℂ := fun i => (l (Sum.inl i) : ℂ) with hp
  set p' : Fin g → ℂ := fun i => (l' (Sum.inl i) : ℂ) with hp'
  set q' : Fin g → ℂ := fun i => (l' (Sum.inr i) : ℂ) with hq'
  have h1 : (fun i => (((l + l') (Sum.inl i) : ℝ) : ℂ)) = p + p' := by
    ext i; simp [hp, hp']
  have h2 : (p ᵥ* τ) ⬝ᵥ p' = (p' ᵥ* τ) ⬝ᵥ p := by
    rw [← Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hτ.eq, dotProduct_comm]
  have h3 : ∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ) = p ⬝ᵥ q' := rfl
  simp only [thetaExp, per, h1, h3, ← hp, ← hp', ← hq', Matrix.add_vecMul, add_dotProduct,
    dotProduct_add]
  rw [dotProduct_comm p (p' ᵥ* τ), h2]
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
