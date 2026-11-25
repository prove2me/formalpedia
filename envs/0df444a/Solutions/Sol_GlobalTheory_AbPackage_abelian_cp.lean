-- Prove2me | solution 1 for GlobalTheory.AbPackage.abelian_cp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:39:14.608611+00:00
-- url     : https://prove2.me/submissions/ba85d119-1c4f-4116-9fce-88852d009b37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_IsCPPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AbelianSchemeCubicalBundleExistsAndMaps
import Theorems.Thm_GlobalTheory_AbPackage_exists_cp
import Theorems.Thm_GlobalTheory_AbPackage_exists_isCPMap_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.AbPackage
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
namespace GlobalTheory.AbPackage
theorem _root_.solution : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → (∀ L : RigLB B, (∃ t : LB.Gen (Theta B L.L), t.IsGen) → (∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) → ∃ M : CP B, M.L = L) ∧ ∀ (S' : Scheme.{0}) (f : S' ⟶ S) (B' : Over S') [GrpObj B'] [IsCommMonObj B'], IsAbelianScheme B' → ∀ (M : CP B) (M' : CP B') (β : B'.left ⟶ B.left), IsGrpPullback B' B f β → (∃ r : LB.Gen (M'.L.L.pull (eSec B')), r.IsGen) → LBIso M'.L.L (M.L.L.pull β) → IsCPPullback M' M f β) := by
  intro hG S B _ _ hB
  refine ⟨exists_cp hG hB, fun S' f B' _ _ hB' M M' β h _ ⟨w, hg⟩ => ⟨h, ?_⟩⟩
  exact exists_isCPMap_of_iso hG hB' M M'
    (fun T x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm) w hg
end GlobalTheory.AbPackage
