-- Prove2me | solution 1 for GlobalTheory.TorsionIntegral.gm_mem_fracUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:38:39.011547+00:00
-- url     : https://prove2.me/submissions/a6a1d27b-e60c-4251-95fe-13b0f7e724d6

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
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.TorsionIntegral
theorem _root_.solution [IsAffine Y] (φ : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : φ z ∈ U) (a : Γ(Y, U)ˣ) :
    gm φ z U a ∈ fracUnits (germTop φ z) := by
  let _ := Y.presheaf.algebra_section_stalk (U := ⊤) ⟨φ z, trivial⟩
  have hl := (isAffineOpen_top Y).isLocalization_stalk ⟨φ z, trivial⟩
  obtain ⟨⟨p, q⟩, e⟩ := @IsLocalization.surj _ _ _ _ _ _ hl ((Y.presheaf.germ U (φ z) h).hom a.val)
  have hq := @IsLocalization.map_units _ _ _ _ _ _ hl q
  have k : ∀ x : Γ(Y, ⊤), germTop φ z x = (φ.stalkMap z).hom ((Y.presheaf.germ ⊤ (φ z) trivial).hom x) :=
    fun x => (Scheme.Hom.germ_stalkMap_apply φ ⊤ z trivial x).symm
  refine ⟨p, q, ?_, ?_⟩
  · rw [k]; exact hq.map _
  · rw [k, k, gm_val φ z U h, ← Scheme.Hom.germ_stalkMap_apply, ← map_mul]
    exact congrArg _ e
end GlobalTheory.TorsionIntegral
