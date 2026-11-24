-- Prove2me | solution 1 for GlobalTheory.Cartier.SecMaps.nonzeroLocus_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:09:28.979811+00:00
-- url     : https://prove2.me/submissions/cde17068-cfad-4e89-8113-90b34657da40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_mem_nonzeroLocus_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


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
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
namespace SecMaps
theorem _root_.solution {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B}
    {a : A.Sec} {b : B.Sec} (h : SecMaps w a b) : Out.nonzeroLocus a = Out.nonzeroLocus b := by
  ext x
  obtain ⟨q, hq⟩ := LB.mem_of_cover hA x
  obtain ⟨p, hp⟩ := LB.mem_of_cover hB x
  have hm : x ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  have e := congrArg (X.presheaf.germ (B.U p ⊓ A.U q) x hm).hom (h (p, q))
  rw [map_mul, germ_resG, germ_resG] at e
  refine (mem_nonzeroLocus_iff a q hq).trans (Iff.trans ?_ (mem_nonzeroLocus_iff b p hp).symm)
  rw [X.mem_basicOpen _ x hq, X.mem_basicOpen _ x hp]
  refine Iff.trans ?_ (iff_of_eq (congrArg IsUnit e)).symm
  rw [IsUnit.mul_iff]
  exact ⟨fun h => ⟨(Units.isUnit _).map _, h⟩, fun h => h.2⟩
end SecMaps
end GlobalTheory.Cartier
