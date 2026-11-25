-- Prove2me | solution 1 for GlobalTheory.TanBasisLocal.dual_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:40:53.327529+00:00
-- url     : https://prove2.me/submissions/3d84bcab-744f-4a3c-8007-b113e875cd22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsTangentVectorBasisAtPointBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TanBasisLocal
import Theorems.Thm_Formalism_L2_Pj_dualMap_comp
import Theorems.Thm_Formalism_L2_Pj_spMap_comp_ring
import Theorems.Thm_GlobalTheory_Frames_existsUnique_glue_dual
import Theorems.Thm_GlobalTheory_SqZero_dualMap_comp


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
open GlobalTheory GlobalTheory.TanBasisLocal
namespace GlobalTheory.TanBasisLocal
theorem _root_.solution {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {w w' : Sp (DualNumber S) ⟶ Y}
    (e : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w =
      spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w') : w = w' := by
  have key := GlobalTheory.Frames.existsUnique_glue_dual S Y n h hs
    (fun i => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w') (by
      intro i j α β hα hβ
      rw [← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, ← dualMap_comp, ← dualMap_comp,
        hα, hβ])
  exact key.unique e (fun _ => rfl)
end GlobalTheory.TanBasisLocal
