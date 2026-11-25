-- Prove2me | solution 1 for GlobalTheory.Published.principalPolarisationOneSection.of_h0Field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:05:58.918044+00:00
-- url     : https://prove2.me/submissions/ed7c4c90-33cb-41e3-9d5e-00106227e49a

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
theorem _root_.solution (h : GlobalSectionsRankAlgClosed) : principalPolarisationOneSection := by
  intro K _ _ P
  simpa using h K P 1 le_rfl
end GlobalTheory.Published.principalPolarisationOneSection
