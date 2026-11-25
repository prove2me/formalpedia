-- Prove2me | solution 1 for GlobalTheory.HypOrbitUnique.pull_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:25:04.779101+00:00
-- url     : https://prove2.me/submissions/e61f3a37-fc68-4043-9851-1d0bf24c8861

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasureOrbitRepresentation
import Theorems.Thm_GlobalTheory_HypOrbitUnique_inc_closedEmbedding
import Theorems.Thm_PI_RhsWLim_W_HU_pull_apply
import Theorems.Thm_PI_RhsWLim_W_HU_pull_left
import Theorems.Thm_PI_RhsWLim_W_HU_pull_sigmaFinite
import Theorems.Thm_PI_RhsWLim_W_gauge_ball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HypOrbitUnique
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU PI.RhsWLim.W.MB
variable {k r : ℕ}
namespace GlobalTheory.HypOrbitUnique
theorem _root_.solution (ν : Measure (Mt k r)) (hG : IsGaugeOn k r (UWb k r) ν) {K : Set (Gp k r)}
    (hK : IsCompact K) : pull ν K ≠ ⊤ := by
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  obtain ⟨⟨hσ, hne, hc, hl⟩, -⟩ := hG
  haveI : LocallyCompactSpace (Gp k r) := inc_closedEmbedding.locallyCompactSpace
  haveI : T2Space (Gp k r) := inc_closedEmbedding.isEmbedding.t2Space
  haveI := pull_sigmaFinite ν
  haveI := pull_left ν hl
  have key := measure_eq_div_smul (Measure.haar : Measure (Gp k r)) (pull ν) (s := inc ⁻¹' bBall k r ρ)
    (by rw [pull_apply ν hc]; exact h0.ne') (by rw [pull_apply ν hc]; exact ht.ne)
  set c := (Measure.haar : Measure (Gp k r)) (inc ⁻¹' bBall k r ρ) / pull ν (inc ⁻¹' bBall k r ρ)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at key
    exact NeZero.ne _ key
  have h1 : (Measure.haar : Measure (Gp k r)) K ≠ ⊤ := hK.measure_lt_top.ne
  rw [key, Measure.smul_apply, smul_eq_mul] at h1
  intro htop
  rw [htop, ENNReal.mul_top hc0] at h1
  exact h1 rfl
end GlobalTheory.HypOrbitUnique
