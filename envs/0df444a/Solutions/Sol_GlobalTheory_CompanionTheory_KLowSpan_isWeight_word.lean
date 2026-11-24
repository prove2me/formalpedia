-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KLowSpan.isWeight_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:10:28.413088+00:00
-- url     : https://prove2.me/submissions/96492166-6cbe-4bed-a809-f29d7ee5f916

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kcomm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kwt_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kwt_cons
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
theorem _root_.solution (hF : KRel ε F) (hw : IsWeight F μ w) :
    ∀ (l : List (Fin n × Fin n)), KLower ε l → IsWeight F (kwt μ l) (word F l w) := by
  intro l
  induction l with
  | nil => intro _ c; simpa [kwt_nil] using hw c
  | cons p l ih =>
    intro hl c
    have hl' : KLower ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p (by simp)
    rw [word_cons, Module.End.mul_apply, kcomm_apply hF rfl hp.2, ih hl' c, map_smul]
    simp only [kwt_cons, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : c = p.1 <;> by_cases h2 : p.2 = c
    · subst h1; rw [h2] at *; simp
    · subst h1; simp [h2, Ne.symm h2, add_smul]
    · subst h2; simp [h1, add_smul, sub_eq_add_neg]
    · simp [h1, h2, Ne.symm h2]
end GlobalTheory.CompanionTheory.KLowSpan
