-- Prove2me | solution 1 for GlobalTheory.SpecialFibreGenerator.mem_basicOpen_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:49:57.692929+00:00
-- url     : https://prove2.me/submissions/cdd2682c-ce1b-4095-a958-92b4737e07ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecGeneratesSpecialFibre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
open GlobalTheory
open GlobalTheory.SpecialFibreGenerator
open TopologicalSpace Opposite
variable {X Y : Scheme.{0}}
namespace GlobalTheory.SpecialFibreGenerator
theorem _root_.solution {L : LB X} (s : L.Sec) {a b : L.ι} {x : X} (ha : x ∈ L.U a)
    (hb : x ∈ X.basicOpen (s.f b)) : x ∈ X.basicOpen (s.f a) := by
  have h := congrArg X.basicOpen (s.compat a b)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _)] at h
  have h₁ := X.basicOpen_res (s.f a) (homOfLE (inf_le_left : L.U a ⊓ L.U b ≤ L.U a)).op
  have h₂ := X.basicOpen_res (s.f b) (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op
  have hab : x ∈ L.U a ⊓ L.U b := ⟨ha, X.basicOpen_le _ hb⟩
  exact (h₁.le (h.ge ⟨hab, h₂.ge ⟨hab, hb⟩⟩)).2
end GlobalTheory.SpecialFibreGenerator
