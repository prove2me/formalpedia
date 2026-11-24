-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.sum_mm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:51.78583+00:00
-- url     : https://prove2.me/submissions/b62950af-5a86-4c7b-9c58-29d4ff7ff403

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_dl_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_sum_pt
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSICFRel
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) (i : NC ε) (f : Fin n × Fin n → ℂ) :
    ∑ k : NC ε, mm a b i.1 k.1 * f k.1 = dl i.1.1 a * f (b, i.1.2) - dl i.1.2 b * f (i.1.1, a) := by
  have e : ∀ k : NC ε, mm a b i.1 k.1 * f k.1 =
      dl i.1.1 a * (dl k.1.1 b * dl k.1.2 i.1.2 * f k.1) - dl i.1.2 b * (dl k.1.1 i.1.1 * dl k.1.2 a * f k.1) := by
    intro k
    rw [mm, dl_comm i.1.2 k.1.2, dl_comm i.1.1 k.1.1]; ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  · by_cases h : i.1.1 = a
    · rw [sum_pt ε b i.1.2 (by rw [← hab, ← h]; exact i.2.1) i.2.2]
    · simp [dl, h]
  · by_cases h : i.1.2 = b
    · rw [sum_pt ε i.1.1 a i.2.1 (by rw [hab, ← h]; exact i.2.2)]
    · simp [dl, h]
end GlobalTheory.CompanionTheory.DSICFRel
