-- Prove2me | solution 1 for GlobalTheory.MaxCusp.Cm_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:37:09.46833+00:00
-- url     : https://prove2.me/submissions/6c110a9a-a537-4fe5-99b0-d4cba02ba7f2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaxCusp
open NumberField Complex MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}
variable (X : Data E r)
namespace GlobalTheory.MaxCusp
theorem _root_.solution (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) (v : Fin r → ℂ)
    (i : Fin d) :
    (Cm X u b τ *ᵥ v) i =
      -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (Data.emb τ.1 (u k)) := by
  simp only [Cm, Matrix.mulVec, dotProduct, Matrix.of_apply, hermC]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring
end GlobalTheory.MaxCusp
