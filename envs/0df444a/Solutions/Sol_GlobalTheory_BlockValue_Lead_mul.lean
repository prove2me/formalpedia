-- Prove2me | solution 1 for GlobalTheory.BlockValue.Lead.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:52:54.612799+00:00
-- url     : https://prove2.me/submissions/62bf653d-a99c-4a02-9539-0e28e47c8904

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
open GlobalTheory GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.BlockValue
namespace Lead
theorem _root_.solution {π : σ → κ} {d e : σ →₀ ℕ} {f g : MvPowerSeries σ C} (hf : Lead π d f)
    (hg : Lead π e g) : Lead π (d + e) (f * g) := by
  classical
  have key : ∀ a b : σ →₀ ℕ, MvPowerSeries.coeff a f * MvPowerSeries.coeff b g ≠ 0 →
      (d + e).mapDomain π ≤ (a + b).mapDomain π ∧
        ((a + b).mapDomain π ≤ (d + e).mapDomain π → a = d ∧ b = e) := by
    intro a b hne
    obtain ⟨h1, h2⟩ := hf.1 a (left_ne_zero_of_mul hne)
    obtain ⟨h3, h4⟩ := hg.1 b (right_ne_zero_of_mul hne)
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_add]
    refine ⟨add_le_add h1 h3, fun h => ⟨h2 fun x => ?_, h4 fun x => ?_⟩⟩
    all_goals
      have a1 := h x
      have a2 := h1 x
      have a3 := h3 x
      simp only [Finsupp.add_apply] at a1
      omega
  refine ⟨fun m hm => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_mul] at hm
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨k1, k2⟩ := key _ _ hne
    rw [← hp]
    refine ⟨k1, fun h => ?_⟩
    rw [(k2 h).1, (k2 h).2]
  · rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (d, e)]
    · simp [hf.2, hg.2]
    · intro p hp hpe
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_contra hne
      have := (key _ _ hne).2 (by rw [hp])
      exact hpe (Prod.ext this.1 this.2)
    · intro h
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at h
      exact absurd rfl h
end Lead
end GlobalTheory.BlockValue
