-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.exists_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:55:40.011624+00:00
-- url     : https://prove2.me/submissions/b4cc4a48-331c-48b6-9d2b-04af6485a8b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Theorems.Thm_GlobalTheory_MomOne_Basic_nonempty_iso
import Theorems.Thm_GlobalTheory_MomOne_Basic_exists_ok_of
import Theorems.Thm_GlobalTheory_MomOne_Basic_norm_nat_eq_one

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
theorem _root_.solution (q : ℕ) [Fact q.Prime] : ∃ M : Mdl q, M.Ok := by
  obtain ⟨ι⟩ := nonempty_iso q
  have hq : q.Prime := Fact.out
  by_cases h : q = 37
  · obtain ⟨L, c, H⟩ := exists_ok_of ι ⟨0, -1, 1, 0, 0⟩ (by simp) (by simp) (by simp) (by simp) (by simp) (by
      have : (⟨0, -1, 1, 0, 0⟩ : WeierstrassCurve ℂ_[q]).Δ = -((11 : ℕ) : ℂ_[q]) := by
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        norm_num
      rw [this, norm_neg]; exact norm_nat_eq_one (by subst h; norm_num))
    exact ⟨_, H⟩
  · obtain ⟨L, c, H⟩ := exists_ok_of ι ⟨0, 0, 1, -1, 0⟩ (by simp) (by simp) (by simp) (by simp) (by simp) (by
      have : (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℂ_[q]).Δ = ((37 : ℕ) : ℂ_[q]) := by
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        norm_num
      rw [this]; exact norm_nat_eq_one ((Nat.coprime_primes hq (by norm_num)).2 h))
    exact ⟨_, H⟩
end GlobalTheory.MomOne.Basic
