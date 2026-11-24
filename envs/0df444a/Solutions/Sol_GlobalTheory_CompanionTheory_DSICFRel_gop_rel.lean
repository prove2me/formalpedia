-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.gop_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:03:20.257771+00:00
-- url     : https://prove2.me/submissions/744bd8b1-6190-4127-ab3b-8def9a3a71ad

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_bil_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_dl_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_gop_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_sum_mm
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
theorem _root_.solution (h : CAR) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] :
    KRel ε (Gop ε : Fin n → Fin n → Module.End ℂ (Ch ε V)) := by
  intro a b c d hab hcd
  have hr : ∀ (x y : Fin n) (T : Module.End ℂ (Ch ε V)), (if x = y then T else 0) = dl x y • T := by
    intro x y T; unfold dl; split_ifs <;> simp
  simp only [gop_eq, hr]
  rw [bil_comm cre ann (fun i j => (h n ε V i j).1) (fun i j => (h n ε V i j).2.1)
    (fun i j => by convert (h n ε V i j).2.2)]
  simp only [bil, Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Finset.sum_sub_distrib, sum_mm ε a b hab i (fun k => mm c d k j.1), sum_mm ε c d hcd i (fun k => mm a b k j.1)]
  simp only [mm]
  rw [dl_comm b j.1.1, dl_comm d j.1.1, dl_comm a j.1.2, dl_comm c j.1.2, dl_comm a d, dl_comm c b]
  ring
end GlobalTheory.CompanionTheory.DSICFRel
