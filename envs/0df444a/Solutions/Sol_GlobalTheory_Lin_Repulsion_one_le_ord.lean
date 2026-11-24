-- Prove2me | solution 1 for GlobalTheory.Lin.Repulsion.one_le_ord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:55.493285+00:00
-- url     : https://prove2.me/submissions/52d0a0df-084a-4b45-8a87-8dd0a0936958

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion

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
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion
namespace GlobalTheory.Lin.Repulsion
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {w : ℂ} (hw : w ≠ 1)
    (h0 : LFunction χ w = 0) : 1 ≤ ord χ w := by
  have han : AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro z hz
    exact (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  have hpre : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hne : LFunction χ 2 ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)
  have h2o : analyticOrderAt (LFunction χ) 2 ≠ ⊤ := by
    rw [(han 2 h2).analyticOrderAt_eq_zero.2 hne]; simp
  have htop : analyticOrderAt (LFunction χ) w ≠ ⊤ :=
    han.analyticOrderAt_ne_top_of_isPreconnected hpre h2 hw h2o
  have hz : analyticOrderAt (LFunction χ) w ≠ 0 := by
    rw [Ne, (han w hw).analyticOrderAt_eq_zero]; simpa using h0
  unfold ord analyticOrderNatAt
  rw [Nat.one_le_iff_ne_zero]
  intro h
  rcases ENat.toNat_eq_zero.1 h with h | h
  · exact hz h
  · exact htop h
end GlobalTheory.Lin.Repulsion
