-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Bernstein.stComm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:49:16.370843+00:00
-- url     : https://prove2.me/submissions/29c4ee67-8f5b-4029-9b1b-10ca235cd120

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfMemAdjoin
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementCommutative
import Theorems.Thm_GlobalTheory_CompanionTheory_Bernstein_positionOne_invariantIntegral_exchange_step
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bernstein
namespace GlobalTheory.CompanionTheory.Bernstein
theorem _root_.solution : StComm := by
  unfold StComm
  intro l
  induction l with
  | zero =>
    intro N
    refine ⟨N, ?_⟩
    intro V _ _ _ a _
    have hr : Set.range a = ∅ := Set.range_eq_empty a
    rw [hr, Algebra.adjoin_empty]
    rcases subsingleton_or_nontrivial V with hV | hV
    · have : Module.finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) = 0 :=
        Module.finrank_zero_of_subsingleton
      simp [this]
    · have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
      rw [Subalgebra.finrank_bot]
      nlinarith
  | succ l ih =>
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨0, fun V _ _ _ a _ => by simp⟩
    obtain ⟨K, hK⟩ := ih (4 * N ^ 2)
    exact ⟨K, fun V _ _ _ a hc => positionOne_invariantIntegral_exchange_step l N K hN hK _ V a rfl hc⟩
end GlobalTheory.CompanionTheory.Bernstein
