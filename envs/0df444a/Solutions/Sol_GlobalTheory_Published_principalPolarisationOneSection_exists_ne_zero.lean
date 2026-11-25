-- Prove2me | solution 1 for GlobalTheory.Published.principalPolarisationOneSection.exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:05:55.647338+00:00
-- url     : https://prove2.me/submissions/53f8d772-17c2-4af5-b360-927cf4fdd4e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_AbelianLaws_PrincipalPolarisationOneSection

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
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.principalPolarisationOneSection
namespace GlobalTheory.Published.principalPolarisationOneSection
theorem _root_.solution (h : principalPolarisationOneSection) (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) :
    ∃ s : SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K))), s ≠ 0 := by
  by_contra hs
  push Not at hs
  have : Subsingleton (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) :=
    ⟨fun a b => (hs a).trans (hs b).symm⟩
  have : Nontrivial Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
  have h1 := h K P
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1
end GlobalTheory.Published.principalPolarisationOneSection
