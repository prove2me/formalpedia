-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.discr_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:29.741958+00:00
-- url     : https://prove2.me/submissions/325a0c8c-cad5-4957-bc36-32d417ab1eb9

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
open PowerSeries
open scoped ComplexConjugate
variable {q : ℕ} [Fact q.Prime]
open Filter Topology
namespace GlobalTheory.MomOne.Basic
namespace _root_.GlobalTheory.MomOne.Basic
theorem _root_.solution {d : ℕ} {L : PeriodPair}
    (h : _root_.GlobalTheory.MomOne.IsOK d L) :
    _root_.GlobalTheory.MomOne.discr d = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ∧
      _root_.GlobalTheory.MomOne.discr d ≠ 0 := by
  have hG : ∀ k, 0 < k → _root_.GlobalTheory.MomOne.eis d k = L.G (2 * k) := by
    intro k hk
    unfold _root_.GlobalTheory.MomOne.eis PeriodPair.G
    have e1 := tsum_subtype {w : ℂ | _root_.GlobalTheory.MomOne.InOK d w ∧ w ≠ 0}
      (fun w : ℂ => 1 / w ^ (2 * k))
    have e2 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    ext z
    by_cases hz : z = 0
    · subst hz
      have : (2 * k) ≠ 0 := by omega
      simp [Set.indicator, zero_pow this]
    · have hz' : z ∈ (L.lattice : Set ℂ) ↔ _root_.GlobalTheory.MomOne.InOK d z := h z
      by_cases hm : _root_.GlobalTheory.MomOne.InOK d z
      · simp [Set.indicator, hz, hm, hz'.2 hm]
      · simp [Set.indicator, hm, mt hz'.1 hm]
  have hdisc : _root_.GlobalTheory.MomOne.discr d = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
    unfold _root_.GlobalTheory.MomOne.discr PeriodPair.g₂ PeriodPair.g₃
    rw [hG 2 (by norm_num), hG 3 (by norm_num)]
  refine ⟨hdisc, ?_⟩
  rw [hdisc, ← _root_.GlobalTheory.latticeCurve_Δ]
  exact _root_.GlobalTheory.latticeCurve_Δ_ne_zero L
end _root_.GlobalTheory.MomOne.Basic
end GlobalTheory.MomOne.Basic
