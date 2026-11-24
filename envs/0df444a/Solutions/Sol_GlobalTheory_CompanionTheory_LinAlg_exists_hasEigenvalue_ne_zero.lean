-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LinAlg.exists_hasEigenvalue_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:35.703858+00:00
-- url     : https://prove2.me/submissions/2ea5a75e-f7c4-4f88-877f-0a57a47e34a8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsJointEigenvectorNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LinAlg
open Module
namespace GlobalTheory.CompanionTheory.LinAlg
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (T : End ℂ W) (v : W) (m : ℕ) (hm : finrank ℂ W ≤ m)
    (hv : (T ^ m) v ≠ 0) : ∃ μ : ℂ, μ ≠ 0 ∧ T.HasEigenvalue μ := by
  by_contra hno
  push_neg at hno
  have hbot : ∀ μ : ℂ, μ ≠ 0 → T.maxGenEigenspace μ = ⊥ := by
    intro μ hμ
    by_contra hne
    rw [End.maxGenEigenspace_eq_genEigenspace_finrank] at hne
    exact hno μ hμ (End.hasEigenvalue_of_hasGenEigenvalue (k := finrank ℂ W) hne)
  have htop : T.maxGenEigenspace 0 = ⊤ := by
    rw [eq_top_iff, ← End.iSup_maxGenEigenspace_eq_top T]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ = 0
    · rw [hμ]
    · rw [hbot μ hμ]
      exact bot_le
  have hvm : v ∈ T.maxGenEigenspace 0 := htop ▸ Submodule.mem_top
  rw [End.maxGenEigenspace_eq_genEigenspace_finrank, End.mem_genEigenspace_nat] at hvm
  simp only [zero_smul, sub_zero, LinearMap.mem_ker] at hvm
  apply hv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm, pow_add, Module.End.mul_apply, hvm, map_zero]
end GlobalTheory.CompanionTheory.LinAlg
