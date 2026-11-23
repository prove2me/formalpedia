-- Prove2me | solution 1 for GlobalTheory.Cartier.germK_eq_mul_ratOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:06.511656+00:00
-- url     : https://prove2.me/submissions/33e58c10-92b5-4791-894f-2d1e47fd5d19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_germ
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_ne_zero

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
theorem _root_.solution {L : LB X} (hL : L.IsLB) {s : L.Sec} (hs : IsRegularSec s)
    (V : X.Opens) [Nonempty V] {t : ∀ i, Γ(X, V ⊓ L.U i)} (ht : t ∈ secOn L V) (i : L.ι)
    [Nonempty (V ⊓ L.U i : X.Opens)] :
    (X.germToFunctionField _).hom (t i) =
      (X.germToFunctionField (V ⊓ L.U i)).hom (resG X inf_le_right (s.f i)) * ratOf hL s V t := by
  have hi : genericPoint X ∈ V ⊓ L.U i := genericPoint_mem _
  have h0 := mem_genericChart hL
  have hm : genericPoint X ∈ V ⊓ L.U i ⊓ L.U (genericChart hL) := ⟨hi, h0⟩
  have hm' : genericPoint X ∈ L.U i ⊓ L.U (genericChart hL) := ⟨hi.2, h0⟩
  have e₁ := congrArg (X.presheaf.germ _ _ hm).hom (ht i (genericChart hL))
  have e₂ := congrArg (X.presheaf.germ _ _ hm').hom (s.compat i (genericChart hL))
  rw [map_mul, germ_resG, germ_resG, germ_resG] at e₁
  rw [map_mul, germ_resG, germ_resG] at e₂
  have hne : @id X.functionField ((X.presheaf.germ _ _ h0).hom (s.f (genericChart hL))) ≠ 0 :=
    nonZeroDivisors.ne_zero (isRegularFn_iff_germ.1 (hs _) _ h0)
  have key : ∀ g a b : X.functionField, b ≠ 0 → g * a = g * b * (a * b⁻¹) := fun g a b hb => by
    field_simp
  refine e₁.trans ((key _ _ _ hne).trans ?_)
  exact congrArg (· * ratOf hL s V t) (e₂.symm.trans
    (germ_resG (inf_le_right : V ⊓ L.U i ≤ L.U i) _ hi (s.f i)).symm)
end GlobalTheory.Cartier
