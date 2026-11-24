-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSChainAdj.adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:01:29.9228+00:00
-- url     : https://prove2.me/submissions/bf6b6ec3-d225-441c-b196-3d8513d622fc

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SumInsertErase
import Theorems.Thm_GlobalTheory_CompanionTheory_DSChainAdj_term_adj
import Theorems.Thm_GlobalTheory_CompanionTheory_DSChainAdj_ip_sum_left
import Theorems.Thm_GlobalTheory_CompanionTheory_DSChainAdj_ip_sum_right
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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GlobalTheory.CompanionTheory.DSChainAdj
theorem _root_.solution : CompanionTheory.D.DSIC.Adj := by
  intro n ε V _ _ E hE w x
  unfold bd bdA cob
  rw [LinearMap.sum_apply, LinearMap.sum_apply, ip_sum_left, ip_sum_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  refine term_adj i _ _ (fun a b => ?_) w x
  have h := hE i.1.1 i.1.2 a b
  have h1 := i.2.1
  have h2 := i.2.2
  rw [h]
  simp [Formalism.REAL.sgn, h1, h2]
end GlobalTheory.CompanionTheory.DSChainAdj
