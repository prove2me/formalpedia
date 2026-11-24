-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZetaHighest.wt_false
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:02.655255+00:00
-- url     : https://prove2.me/submissions/fd62c4a9-53a1-40a5-b58a-36a9994104da

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkStrictMono
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
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZetaHighest
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.ZetaHighest
theorem _root_.solution (ε : Fin n → Bool) (c : Fin n) (hc : ε c = false) :
    wtA (A1 ε) c = -((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) := by
  have h1 : ((A1 ε).filter fun i => i.1.1 = c) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun i _ h => ?_
    have := i.2.1
    rw [h, hc] at this
    exact Bool.false_ne_true this
  have h2 : ((A1 ε).filter fun i => i.1.2 = c).card = (univ.filter fun b => c < b ∧ ε b ≠ ε c).card := by
    refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · intro i hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi ⊢
      refine ⟨hi.2 ▸ hi.1, ?_⟩
      rw [i.2.1, hc]; simp
    · intro i hi j hj h
      simp only [A1, mem_filter, mem_univ, true_and] at hi hj
      exact Subtype.ext (Prod.ext h (hi.2.trans hj.2.symm))
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      refine ⟨⟨(a, c), ?_, hc⟩, ?_, rfl⟩
      · have := ha.2; rw [hc] at this; simpa using this
      · simp only [A1, mem_filter, mem_univ, true_and]
        exact ⟨ha.1, trivial⟩
  unfold wtA
  rw [h1, h2]; simp
end GlobalTheory.CompanionTheory.ZetaHighest
