-- Prove2me | solution 1 for GlobalTheory.BoxCompare.isNormSymm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:51:05.067845+00:00
-- url     : https://prove2.me/submissions/3b7ea409-958a-45cd-b7b6-c32e19137498

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PowerGroupDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RestrictLineBundleSymmetryUnitsEquivIsoApply
import Theorems.Thm_GlobalTheory_BoxCompare_isGen_symEquiv
import Theorems.Thm_GlobalTheory_BoxCompare_corr_iff_diagOne
import Theorems.Thm_GlobalTheory_BoxCompare_diagOne_iff_fixesRig
import Theorems.Thm_GlobalTheory_BoxCompare_maps_iff_fixesRig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxCompare
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LB
open GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum (PowerDatum IsNormSymm)
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.BoxCompare
theorem _root_.solution (L : RigLB G) (sy : SymGen L.L (ι[G]).left) :
    IsNormSymm L (symEquiv L.L _ sy) ↔ IsCanonSym L.L sy := by
  have he : eSec G ≫ (ι[G]).left = eSec G := GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv.trans (Category.id_comp _)
  refine (and_congr (isGen_symEquiv L.L _ sy) (maps_iff_fixesRig L.L L.rig sy)).trans ?_
  exact and_congr_right fun hsy => ((corr_iff_diagOne L.L _ _ he sy).trans
    (diagOne_iff_fixesRig L.L _ _ L.isLB sy hsy L.rig L.rigGen)).symm
end GlobalTheory.BoxCompare
