-- Prove2me | solution 1 for GlobalTheory.of_isPullback_openCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:20.078201+00:00
-- url     : https://prove2.me/submissions/9f424081-a2af-4af4-9385-198c2452a876

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFlatSurjectiveClosedSubschemeOfOpenCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {B T : Scheme.{0}} (f : B ⟶ T) {ι : Type} (V : ι → T.Opens) (hV : iSup V = ⊤)
    (A : ι → Scheme.{0}) (k : ∀ i, A i ⟶ B) (g : ∀ i, A i ⟶ (V i).toScheme)
    (h : ∀ i, IsPullback (k i) (g i) f (V i).ι) (hg : ∀ i, P (g i)) : P f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) V hV]
  intro i
  have h' := (isPullback_morphismRestrict f (V i)).flip
  have e : (h'.isoIsPullback _ _ (h i)).hom ≫ g i = f ∣_ V i := by simp
  rw [← e]
  exact (P.cancel_left_of_respectsIso _ _).2 (hg i)
end GlobalTheory
