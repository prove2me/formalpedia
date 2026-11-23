-- Prove2me | solution 1 for GlobalTheory.Cartier.mem_ratSecs_iff_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:41.783808+00:00
-- url     : https://prove2.me/submissions/aeea5a8d-06d8-4a3f-bd19-6d18b0295377

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_exists_germK_eq_of_stalk

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
variable [IsIntegral X]
namespace GlobalTheory.Cartier
theorem _root_.solution {L : LB X} (s : L.Sec) (V : X.Opens) [Nonempty V]
    (h : X.functionField) :
    h ∈ ratSecs s V ↔ ∀ (i : L.ι) (x : X) (_ : x ∈ V) (hx : x ∈ L.U i),
      algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ _ x hx).hom (s.f i)) * h ∈
        Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  constructor
  · intro hh i x hxV hx
    have hm : x ∈ V ⊓ L.U i := ⟨hxV, hx⟩
    have : Nonempty (V ⊓ L.U i : X.Opens) := ⟨⟨x, hm⟩⟩
    obtain ⟨a, ha⟩ := hh i
    refine ⟨(X.presheaf.germ _ x hm).hom a, ?_⟩
    rw [← germ_resG (inf_le_right : V ⊓ L.U i ≤ L.U i) x hm]
    exact (Scheme.algebraMap_germ_eq_germToFunctionField X hm a).trans (ha.trans
      (congrArg (· * h) (Scheme.algebraMap_germ_eq_germToFunctionField X hm _).symm))
  · intro hh i _
    refine exists_germK_eq_of_stalk _ _ fun x hx => ?_
    have := hh i x hx.1 hx.2
    rw [← germ_resG (inf_le_right : V ⊓ L.U i ≤ L.U i) x hx] at this
    exact (congrArg (fun r => r * h ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField))
      (Scheme.algebraMap_germ_eq_germToFunctionField X hx _)).mp this
end GlobalTheory.Cartier
