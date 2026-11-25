-- Prove2me | solution 1 for GlobalTheory.TorsionIntegral.gm_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:33:06.341736+00:00
-- url     : https://prove2.me/submissions/58e1bcd9-a369-44ac-b2d0-7c158d76374f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral
namespace GlobalTheory.TorsionIntegral
theorem _root_.solution {Y Z : Scheme.{0}} [IsAffine Y] [IsIntegral Y] (φ : Z ⟶ Y) (z : Z)
    (hφ : Function.Injective (germTop φ z)) (U : Y.Opens) (h : φ z ∈ U) : Function.Injective (gm φ z U) := by
  let _ := Y.presheaf.algebra_section_stalk (U := ⊤) ⟨φ z, trivial⟩
  have hl := (isAffineOpen_top Y).isLocalization_stalk ⟨φ z, trivial⟩
  have hs : Function.Injective (φ.stalkMap z).hom := (injective_iff_map_eq_zero _).2 fun x hx => by
    obtain ⟨⟨p, q⟩, e⟩ := @IsLocalization.surj _ _ _ _ _ _ hl x
    have hq := @IsLocalization.map_units _ _ _ _ _ _ hl q
    have k : germTop φ z p = (φ.stalkMap z).hom (x * _) :=
      (Scheme.Hom.germ_stalkMap_apply φ ⊤ z trivial p).symm.trans (congrArg _ e.symm)
    rw [map_mul, hx, zero_mul] at k
    have hp : p = 0 := hφ (k.trans (map_zero _).symm)
    subst hp
    exact hq.mul_left_eq_zero.1 (e.trans (map_zero _))
  intro a b e
  have e' := congrArg Units.val e
  rw [gm_val φ z U h, gm_val φ z U h, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  exact Units.ext (germ_injective_of_isIntegral Y (φ z) h (hs e'))
end GlobalTheory.TorsionIntegral
