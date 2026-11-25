-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.isTranslatedPull_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:53:31.385652+00:00
-- url     : https://prove2.me/submissions/f9adf105-b98e-4103-b091-eb998685e941

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_EndomorphismPullbackRigid
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EndomorphismPullbackRigid_trivIso_isGen
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EndomorphismPullbackRigid_isoVal_trivIso
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EndomorphismPullbackRigid_secVal_trivOne
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EndomorphismPullbackRigid_rigVal_trivRig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} {A : Over X}
variable [GrpObj A] [IsCommMonObj A]
namespace GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
theorem _root_.solution (φ : A ⟶ A) [IsMonHom φ] {N : ℕ} (hN : Odd N) {T : Over X}
    (b : T ⟶ A) (hb : b ^ N = 1) :
    IsTranslatedPull (trivRig A) φ N b (trivOne 1 T) (trivOne N T) := by
  refine ⟨trivOne N T, ⟨trivIso _ _ _, ⟨trivIso_isGen _ _ _, ?_⟩, ?_⟩, hN, hb, trivIso _ _ _,
    trivIso _ _ _, ⟨trivIso_isGen _ _ _, ?_⟩, trivIso_isGen _ _ _, ?_, ?_, ?_⟩
  all_goals
    intro W t
    intros
    simp [isoVal_trivIso, secVal_trivOne, rigVal_trivRig]
end GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
