-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeOpen.eq_bot_of_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:04.299343+00:00
-- url     : https://prove2.me/submissions/16ba88d8-cf26-40c9-913e-42923c026e9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre

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
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeOpen
namespace GlobalTheory.AbLaw.CubeOpen
theorem _root_.solution {S : Type} [CommRing S] [IsLocalRing S] (J : Ideal S) (hJ : J.FG)
    (H : ∀ (I' : Ideal S) (e : S), e ∈ J → IsLocalRing.maximalIdeal S * J ≤ I' → I' ≤ J →
      J ≤ I' ⊔ Ideal.span {e} → J ≤ I') : J = ⊥ := by
  classical
  have key : ∀ s : Finset S, (s : Set S) ⊆ J →
      J ≤ IsLocalRing.maximalIdeal S * J ⊔ Ideal.span (s : Set S) →
      J ≤ IsLocalRing.maximalIdeal S * J := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ h; simpa using h
    | insert a s _ ih =>
      intro hs h
      rw [Finset.coe_insert] at hs h
      have hs' : (s : Set S) ⊆ J := (Set.subset_insert _ _).trans hs
      refine ih hs' (H _ a (hs (Set.mem_insert _ _)) le_sup_left
        (sup_le Ideal.mul_le_right (Ideal.span_le.2 hs')) ?_)
      rwa [Ideal.span_insert, sup_comm (Ideal.span {a}), ← sup_assoc] at h
  obtain ⟨s, hs⟩ := id hJ
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal S) J hJ ?_
    (IsLocalRing.maximalIdeal_le_jacobson _)
  exact key s (hs ▸ Ideal.subset_span) (hs.ge.trans le_sup_right)
end GlobalTheory.AbLaw.CubeOpen
