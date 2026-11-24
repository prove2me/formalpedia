-- Prove2me | solution 1 for GlobalTheory.AbLaw.Segre.isLB_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:12.554411+00:00
-- url     : https://prove2.me/submissions/11eb217e-e451-40be-a7ff-3c61e5e37f99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Theorems.Thm_GlobalTheory_AbLaw_Segre_ap_g_self
import Theorems.Thm_GlobalTheory_AbLaw_Segre_ap_cocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}
namespace GlobalTheory.AbLaw.Segre
theorem _root_.solution (hH : H.IsLB) (hK : K.IsLB) : (box p q H K).IsLB where
  cover := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ i, K.U i by rw [hK.cover]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  g_self := fun a => by
    refine Units.ext ((rs_mul p q _ _ _ _ _).trans ?_)
    rw [ap_g_self p hH, ap_g_self q hK, _root_.mul_one, Units.val_one]
  cocycle := fun a b c => by
    refine Units.ext ((congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).trans
      (Eq.trans ?_ (rs_mul p q _ _ _ _ _).symm))
    exact (mul_mul_mul_comm _ _ _ _).trans
      (congrArg₂ (· * ·) (ap_cocycle p hH _ _ _ _ _ _).symm (ap_cocycle q hK _ _ _ _ _ _).symm)
end GlobalTheory.AbLaw.Segre
