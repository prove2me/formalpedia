-- Prove2me | solution 1 for GlobalTheory.fix_torsion_of_fix_geometric_of_isDominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:17:13.956258+00:00
-- url     : https://prove2.me/submissions/5af4d424-7179-49bd-9652-de6bd9b9b0e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqOfDominantGeometricPointsOfUnramified
import Theorems.Thm_GlobalTheory_fix_torsion_of_fix_geometric_of_etale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (hmul : MulNSt) {S : Scheme.{0}}
    [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (hM : 1 ≤ M) (hMu : IsUnit (M : Γ(S, ⊤)))
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : P.A ⟶ P.A) (hsm : IsMonHom s)
    (hs : ∀ x : Over.mk t ⟶ P.A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ P.A) (hx : x ^ M = 1) : x ≫ s = x := by
  obtain ⟨hfin, -, -, het, -⟩ := hmul S P M hM
  have := het hMu
  exact fix_torsion_of_fix_geometric_of_etale P.A M t s hs T x hx
end GlobalTheory
