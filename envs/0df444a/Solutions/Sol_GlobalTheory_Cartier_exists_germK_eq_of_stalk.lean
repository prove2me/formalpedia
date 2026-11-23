-- Prove2me | solution 1 for GlobalTheory.Cartier.exists_germK_eq_of_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:01.620155+00:00
-- url     : https://prove2.me/submissions/828aa2c7-85ca-471c-ad60-364cc22e83a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_ext_germK

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
theorem _root_.solution (U : X.Opens) [Nonempty U] (t : X.functionField)
    (h : ∀ x ∈ U, t ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) :
    ∃ a : Γ(X, U), (X.germToFunctionField U).hom a = t := by
  have loc : ∀ x : U, ∃ (V : X.Opens) (_ : V ≤ U) (_ : x.1 ∈ V) (c : Γ(X, V)),
      ∀ hV : genericPoint X ∈ V, (X.presheaf.germ V _ hV).hom c = t := by
    rintro ⟨x, hx⟩
    obtain ⟨r, hr⟩ := h x hx
    obtain ⟨V, hV, c, rfl⟩ := X.presheaf.exists_germ_eq r
    have : Nonempty V := ⟨⟨x, hV⟩⟩
    refine ⟨U ⊓ V, inf_le_left, ⟨hx, hV⟩, resG X inf_le_right c, fun hV' => ?_⟩
    rw [germ_resG, ← hr]
    exact (Scheme.algebraMap_germ_eq_germToFunctionField X hV c).symm
  choose V hV hx c hc using loc
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V U (fun i => homOfLE (hV i))
    (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩) c (fun i j => ext_germK fun hη =>
      ((germ_resG inf_le_left _ hη (c i)).trans (hc i _)).trans
        ((germ_resG inf_le_right _ hη (c j)).trans (hc j _)).symm)
  obtain ⟨x⟩ := ‹Nonempty U›
  have : Nonempty (V x) := ⟨⟨x.1, hx x⟩⟩
  refine ⟨s, ?_⟩
  rw [← hc x (genericPoint_mem _), ← hs x]
  exact (germ_resG (hV x) _ (genericPoint_mem _) s).symm
end GlobalTheory.Cartier
