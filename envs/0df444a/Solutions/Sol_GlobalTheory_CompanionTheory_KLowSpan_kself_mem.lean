-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KLowSpan.kself_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:37:28.654852+00:00
-- url     : https://prove2.me/submissions/694e85e5-5517-4822-8044-ac5777f24a23

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kword_mem
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
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
theorem _root_.solution : w ∈ kLowSpan ε F w := by
  have h := kword_mem (ε := ε) (F := F) (w := w) (l := []) (fun p hp => by simp at hp)
  simpa using h
end GlobalTheory.CompanionTheory.KLowSpan
