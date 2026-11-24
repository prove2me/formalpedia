-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSChainAdj.sum_insert_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:25.641408+00:00
-- url     : https://prove2.me/submissions/bf88d291-d69d-4c2d-9c0f-5210f8d71694

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SumInsertErase
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
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSChainAdj
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.DSChainAdj
theorem _root_.solution (i : NC ε) (f : Finset (NC ε) → Finset (NC ε) → ℂ) :
    (∑ A : Finset (NC ε), if i ∈ A then 0 else f (insert i A) A) =
      ∑ B : Finset (NC ε), if i ∈ B then f B (B.erase i) else 0 := by
  have h1 : (∑ A : Finset (NC ε), if i ∈ A then 0 else f (insert i A) A) =
      ∑ A ∈ univ.filter (fun A : Finset (NC ε) => i ∉ A), f (insert i A) A := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases h : i ∈ A <;> simp [h]
  rw [h1, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun A => insert i A) (fun B => B.erase i) ?_ ?_ ?_ ?_ ?_
  · intro A _
    simp
  · intro B _
    simp
  · intro A hA
    have hA' : i ∉ A := by simpa using hA
    exact Finset.erase_insert hA'
  · intro B hB
    have hB' : i ∈ B := by simpa using hB
    exact Finset.insert_erase hB'
  · intro A hA
    have hA' : i ∉ A := by simpa using hA
    simp only [Finset.erase_insert hA']
end GlobalTheory.CompanionTheory.DSChainAdj
