-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliBlocks.mem_pplus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:24.911236+00:00
-- url     : https://prove2.me/submissions/f92b1cf5-ab56-4364-8463-721d09d79715

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
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
open Finset Equiv
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliBlocks
open Formalism.REAL CompanionTheory.D.DSIC
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CapelliBlocks
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n}
    (ha : ε a = true) (hb : ε b = false) (v : V) : E a b v ∈ pplus ε E := by
  classical
  refine ⟨Pi.single (⟨(a, b), ha, hb⟩ : NC ε) v, ?_⟩
  rw [Finset.sum_eq_single (⟨(a, b), ha, hb⟩ : NC ε)]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp
end GlobalTheory.CompanionTheory.CapelliBlocks
