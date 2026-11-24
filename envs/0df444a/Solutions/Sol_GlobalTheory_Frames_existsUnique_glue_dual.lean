-- Prove2me | solution 1 for GlobalTheory.Frames.existsUnique_glue_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:53.378608+00:00
-- url     : https://prove2.me/submissions/995ee065-fb48-4be9-8e3d-2f32d393cd88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
import Theorems.Thm_GlobalTheory_Frames_existsUnique_glue_dual_of_isTerminal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
noncomputable section
open GlobalTheory GlobalTheory.Frames
namespace GlobalTheory.Frames
theorem _root_.solution : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ w : ∀ i, Sp (DualNumber (Localization.Away (h i))) ⟶ Y, (∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j)) (β : Localization.Away (h j) →+* Localization.Away (h i * h j)), α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → spMap (dualMap α) ≫ w i = spMap (dualMap β) ≫ w j) → ∃! w₀ : Sp (DualNumber S) ⟶ Y, ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = w i :=
  fun _ _ Y _ h hs w hw => existsUnique_glue_dual_of_isTerminal specZIsTerminal Y h hs w hw
end GlobalTheory.Frames
