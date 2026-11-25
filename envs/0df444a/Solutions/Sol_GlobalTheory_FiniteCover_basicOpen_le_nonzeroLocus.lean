-- Prove2me | solution 1 for GlobalTheory.FiniteCover.basicOpen_le_nonzeroLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:42.225309+00:00
-- url     : https://prove2.me/submissions/fd811e5d-1017-4a75-a009-7e268801e807

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinrankSecPullSandwich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FiniteCover
variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
omit [IsIntegral X]
namespace GlobalTheory.FiniteCover
theorem _root_.solution {H : LB X} (s s' : LB.Sec H) (r : Γ(X, nonzeroLocus s))
    (h : ∀ k, rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s'.f k) =
      rs X (inf_le_left : nonzeroLocus s ⊓ H.U k ≤ nonzeroLocus s) r *
        rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k)) :
    X.basicOpen r ≤ nonzeroLocus s' := by
  intro x hx
  have hs : x ∈ nonzeroLocus s := X.basicOpen_le r hx
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  have e := congrArg X.basicOpen (h l)
  rw [Scheme.basicOpen_mul] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ nonzeroLocus s ⊓ H.U l := ⟨hs, X.basicOpen_le _ hl⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, (e.ge ⟨⟨hx', hx⟩, hx', hl⟩).2⟩
end GlobalTheory.FiniteCover
