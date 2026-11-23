-- Prove2me | solution 1 for GlobalTheory.Cartier.isRegularFn_iff_germ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:34.295706+00:00
-- url     : https://prove2.me/submissions/7e7ce21a-25d8-4437-a7eb-b5ec42481e17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_ext_germ

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
theorem _root_.solution {U : X.Opens} {a : Γ(X, U)} :
    IsRegularFn a ↔ ∀ x (hx : x ∈ U),
      (X.presheaf.germ U x hx).hom a ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  constructor
  · intro ha x hx
    refine mem_nonZeroDivisors_iff_right.2 fun t ht => ?_
    obtain ⟨V, hV, b, rfl⟩ := X.presheaf.exists_germ_eq t
    have hm : x ∈ U ⊓ V := ⟨hx, hV⟩
    have e : (X.presheaf.germ (U ⊓ V) x hm).hom (resG X inf_le_right b * resG X inf_le_left a) =
        (X.presheaf.germ (U ⊓ V) x hm).hom 0 := by
      rw [map_mul, germ_resG, germ_resG, map_zero]; exact ht
    obtain ⟨W, hW, i₁, i₂, e'⟩ := X.presheaf.germ_eq x hm hm _ _ e
    have le : W ≤ U ⊓ V := i₁.le
    have e'' : resG X le (resG X inf_le_right b * resG X inf_le_left a) = resG X le 0 := e'
    rw [map_mul, resG_resG, resG_resG, map_zero] at e''
    have hb := mem_nonZeroDivisors_iff_right.1 (ha W _) _ e''
    rw [← germ_resG (le.trans inf_le_right) x hW b, hb, map_zero]
  · intro h V hV
    refine mem_nonZeroDivisors_iff_right.2 fun t ht => ext_germ fun x hx => ?_
    have := congrArg (X.presheaf.germ V x hx).hom ht
    rw [map_mul, germ_resG, map_zero] at this
    rw [map_zero]
    exact mem_nonZeroDivisors_iff_right.1 (h x (hV hx)) _ this
end GlobalTheory.Cartier
