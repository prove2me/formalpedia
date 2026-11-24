-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.main_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:57.59685+00:00
-- url     : https://prove2.me/submissions/a07930b2-efef-4e2a-baa6-08e58d6de595

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution {θ : ℤ} {β δ u : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hδ : 0 < δ) (hδβ : δ ≤ 1 - β)
    (hu : 1 ≤ u) (hl : 4 ≤ Real.log u) : δ * u ≤ mainPsi θ β u ∧ mainPsi θ β u ≤ 3 * u := by
  have hu0 : 0 < u := by linarith
  have hp : 0 < u ^ β := Real.rpow_pos_of_pos hu0 β
  have h1 : u ^ β ≤ u := by
    simpa using Real.rpow_le_rpow_of_exponent_le hu (show β ≤ 1 by linarith)
  have h2 : 0 < u ^ β / β := by positivity
  have h3 : u ^ β / β ≤ 2 * u := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h4 : δ * u ≤ u := by nlinarith
  unfold mainPsi
  rcases hθ with rfl | rfl | rfl
  · simp; constructor <;> linarith
  · have e : u = u ^ β * Real.exp ((1 - β) * Real.log u) := by
      rw [Real.rpow_def_of_pos hu0, ← Real.exp_add]
      rw [show Real.log u * β + (1 - β) * Real.log u = Real.log u by ring, Real.exp_log hu0]
    have h5 : 1 + 4 * (1 - β) ≤ Real.exp ((1 - β) * Real.log u) := by
      have := Real.add_one_le_exp ((1 - β) * Real.log u)
      nlinarith
    have h6 : u ^ β * (1 + 4 * (1 - β)) ≤ u := by
      have := mul_le_mul_of_nonneg_left h5 hp.le
      linarith
    have h7 : u ^ β / β ≤ β * u := by
      rw [div_le_iff₀ (by linarith)]
      have h8 : 1 ≤ (1 + 4 * (1 - β)) * (β * β) := by
        have : 0 ≤ 1 - β := by linarith
        have h9 : 3 / 4 ≤ β * β := by nlinarith
        nlinarith
      have := mul_le_mul_of_nonneg_left h8 hp.le
      have := mul_le_mul_of_nonneg_right h6 (show 0 ≤ β * β by positivity)
      nlinarith
    push_cast
    constructor <;> nlinarith
  · push_cast
    constructor <;> linarith
end GlobalTheory.Lin.PsiToPi
