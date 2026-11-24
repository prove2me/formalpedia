-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:43:56.122538+00:00
-- url     : https://prove2.me/submissions/1f615db6-689e-4db4-8fd8-5c819423d940

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BurnsideSurjOfIrred
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SimpleOfCommutativeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_finrank_sq_le_of_span
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_Burnside_burnside_surj_of_irred
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
noncomputable section
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl
namespace GlobalTheory.CompanionTheory.RgFl
theorem _root_.solution : StComm → StSimple := by
  intro h d l
  obtain ⟨C, hC⟩ := h l (2 * d ^ 2)
  refine ⟨C, fun A _ _ hA V _ _ _ ρ hirr => ?_⟩
  obtain ⟨x, y, a, hcomm, hs⟩ := hA
  rcases subsingleton_or_nontrivial V with hV | hV
  · simp [Module.finrank_zero_of_subsingleton]
  have hsurj := GlobalTheory.CompanionTheory.Burnside.burnside_surj_of_irred ρ hirr
  have h1 := finrank_sq_le_of_span ρ hsurj x y a hs
  have h2 := hC V (fun i => ρ (a i)) (fun i j => (hcomm i j).map ρ)
  have hm : 0 < Module.finrank ℂ V := Module.finrank_pos
  generalize Module.finrank ℂ V = m at *
  generalize Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) = b at *
  have h3 : m * m ≤ C * m := by nlinarith
  exact Nat.le_of_mul_le_mul_right h3 hm
end GlobalTheory.CompanionTheory.RgFl
