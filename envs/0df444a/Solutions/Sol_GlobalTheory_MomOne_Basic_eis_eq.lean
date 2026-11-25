-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.eis_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:31.983327+00:00
-- url     : https://prove2.me/submissions/75064883-545e-4083-81e6-fcb636ed5cbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology
namespace GlobalTheory.MomOne.Basic
theorem _root_.solution {d : ℕ} {L : PeriodPair} (h : IsOK d L) {k : ℕ} (hk : 0 < k) : eis d k = L.G (2 * k) := by
  have h1 : eis d k = ∑' w : ({w : ℂ | InOK d w ∧ w ≠ 0} : Set ℂ), (fun z : ℂ => (z ^ (2 * k))⁻¹) w := by
    simp only [eis, one_div]; rfl
  have h2 : L.G (2 * k) = ∑' w : (L.lattice : Set ℂ), (fun z : ℂ => (z ^ (2 * k))⁻¹) w := rfl
  rw [h1, h2, tsum_subtype _ fun z : ℂ => (z ^ (2 * k))⁻¹, tsum_subtype _ fun z : ℂ => (z ^ (2 * k))⁻¹]
  refine tsum_congr fun z => ?_
  by_cases hz : z = 0
  · subst hz; simp [Set.indicator, hk.ne']
  · have e : z ∈ {w : ℂ | InOK d w ∧ w ≠ 0} ↔ z ∈ (L.lattice : Set ℂ) := by simp [hz, h z]
    by_cases hL : z ∈ (L.lattice : Set ℂ)
    · rw [Set.indicator_of_mem hL, Set.indicator_of_mem (e.2 hL)]
    · rw [Set.indicator_of_notMem hL, Set.indicator_of_notMem (fun h' => hL (e.1 h'))]
end GlobalTheory.MomOne.Basic
