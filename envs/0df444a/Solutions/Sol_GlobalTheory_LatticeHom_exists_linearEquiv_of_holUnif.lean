-- Prove2me | solution 1 for GlobalTheory.LatticeHom.exists_linearEquiv_of_holUnif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:10.842333+00:00
-- url     : https://prove2.me/submissions/40c90b16-c40e-4d7b-8833-a876cd461576

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaUnifAVOfLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivOfLifting
import Theorems.Thm_GlobalTheory_LatticeHom_exists_linearEquiv_of_lifting
import Theorems.Thm_GlobalTheory_AbelianExp_exists_holUnif
import Theorems.Thm_GlobalTheory_HolChart_exists_holomorphic_chart
import Theorems.Thm_GlobalTheory_PointsCompact_compactSpace_points_polAV
import Theorems.Thm_GlobalTheory_existsUnique_point_of_ringHom
import Theorems.Thm_GlobalTheory_exists_holomorphic_section_of_etale
import Theorems.Thm_GlobalTheory_holFamily_lift
import Theorems.Thm_GlobalTheory_isTopologicalGroup_complexPoints
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LatticeHom
namespace GlobalTheory.LatticeHom
theorem _root_.solution (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {L L' : LB P.A.left}
    (u : HolUnif P.A L P.g) (u' : HolUnif P.A L' P.g) :
    ∃ T : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u'.ex (T z) = u.ex z := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  obtain ⟨v, -, hv⟩ := @AbelianExp.exists_holUnif hmul hval (@holFamily_lift hval)
    (@isTopologicalGroup_complexPoints hval) (@PointsCompact.compactSpace_points_polAV hval hvalaff)
    (@HolChart.exists_holomorphic_chart hval hvalaff @exists_holomorphic_section_of_etale) P
  obtain ⟨T, hT⟩ := exists_linearEquiv_of_lifting u v hv
  obtain ⟨T', hT'⟩ := exists_linearEquiv_of_lifting u' v hv
  refine ⟨T.trans T'.symm, fun z => ?_⟩
  rw [← hT', ← hT]
  simp
end GlobalTheory.LatticeHom
