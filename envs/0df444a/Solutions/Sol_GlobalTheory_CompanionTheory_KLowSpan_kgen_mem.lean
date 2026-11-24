-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KLowSpan.kgen_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:41.484745+00:00
-- url     : https://prove2.me/submissions/34e4685c-2a27-45d1-8c46-4c9e9c4e775c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kself_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_klower_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kcomm_apply
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil



set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KLowSpan
variable {n : ℕ} {ε : Fin n → Bool}
variable {U : Type} [AddCommGroup U] [Module ℂ U]
variable {F : Fin n → Fin n → Module.End ℂ U} {μ : Fin n → ℝ} {w : U}
namespace GlobalTheory.CompanionTheory.KLowSpan
theorem _root_.solution (hF : KRel ε F) (hw : KHighest ε F μ w) :
    ∀ (l : List (Fin n × Fin n)), KLower ε l → ∀ i j, ε i = ε j → F i j (word F l w) ∈ kLowSpan ε F w := by
  intro l
  induction l with
  | nil =>
    intro _ i j he
    simp only [word_nil, Module.End.one_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hw.2 i j h he]; exact Submodule.zero_mem _
    · rw [hw.1 i]; exact Submodule.smul_mem _ _ kself_mem
    · exact klower_mem h he kself_mem
  | cons p l ih =>
    intro hl i j he
    have hl' : KLower ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p (by simp)
    rw [word_cons, Module.End.mul_apply, kcomm_apply hF he hp.2]
    refine Submodule.add_mem _ (klower_mem hp.1 hp.2 (ih hl' i j he)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs with h
      · exact ih hl' _ _ (by rw [he, h, hp.2])
      · exact Submodule.zero_mem _
    · split_ifs with h
      · exact ih hl' _ _ (by rw [hp.2, h, he])
      · exact Submodule.zero_mem _
end GlobalTheory.CompanionTheory.KLowSpan
