-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:06:16.375149+00:00
-- url     : https://prove2.me/submissions/7be36658-77b8-46cb-94db-794ee556b847

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_exists_torus_root
import Theorems.Thm_GlobalTheory_Ex_NumD_exists_tor_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
namespace GlobalTheory.Ex.RecPeriods
theorem _root_.solution {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) (hN : ∀ b : N.A, ∃ γ : N.Gt, γ.b = b)
    (k : ℕ) (hk : k ≠ 0) (b : N.A) (hb : b ^ k = 1) : ∃ p : N.QT k, p.1.1 = 1 ∧ p.1.2.b = b := by
  obtain ⟨γ, rfl⟩ := hN b
  obtain ⟨t, ht⟩ := (N.exists_tor_iff (γ ^ k)).2 (by rw [NumD.Gt.pow_b, hb])
  obtain ⟨t', rfl⟩ := exists_torus_root k hk t
  refine ⟨⟨(1, γ * (N.tor t')⁻¹), ?_⟩, rfl, by simp⟩
  rw [NumD.mem_QT, mul_pow, inv_pow, ← N.tor_pow, ht, mul_inv_cancel]
  exact N.io_zero.symm
end GlobalTheory.Ex.RecPeriods
