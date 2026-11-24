-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KLowSpan.cdom_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:27:08.812292+00:00
-- url     : https://prove2.me/submissions/908f3e69-7377-4bd0-b4aa-a2b4fc75ddc5

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_isWeight_word
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_cdom_kwt
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_inner_eq_zero_of_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_eq_zero_of_orth
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}
namespace GlobalTheory.CompanionTheory.KLowSpan
theorem _root_.solution (hF : KRel ε E) (hU : KUnit ε E) (hv : IsWeight E μ v) {ν : Fin n → ℝ} {x : V}
    (hx : x ∈ kLowSpan ε E v) (hx0 : x ≠ 0) (hν : IsWeight E ν x) : PI.UpqRep.CDom ε ν μ := by
  by_contra hc
  refine hx0 (eq_zero_of_orth hx fun l hl => ?_)
  refine inner_eq_zero_of_weight hU (isWeight_word hF hv l hl) hν ?_
  rintro rfl
  exact hc (cdom_kwt μ l hl)
end GlobalTheory.CompanionTheory.KLowSpan
