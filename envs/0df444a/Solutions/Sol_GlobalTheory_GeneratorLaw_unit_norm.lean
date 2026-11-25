-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.unit_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:06:47.510897+00:00
-- url     : https://prove2.me/submissions/7c27027f-7589-4ccd-b381-2f3c2480a7a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
import Theorems.Thm_GlobalTheory_GeneratorLaw_exists_good_at
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GeneratorLaw
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {κ : Type} {O : κ → RigLB B} {G : Over S} [GrpObj G]
  {q : G ⟶ B} {u : ∀ k (i : (O k).L.ι), Γ(G.left, q.left ⁻¹ᵁ (O k).L.U i)ˣ}
namespace GlobalTheory.GeneratorLaw
theorem _root_.solution [IsMonHom q] (h : nv O q u η[G] = 1) (k : κ) (z : (𝟙_ (Over S)).left) (i : (O k).L.ι)
    (hi : eSec B z ∈ (O k).L.U i) : gm (eSec G) z (q.left ⁻¹ᵁ (O k).L.U i) (u k i) *
      gm (𝟙 (𝟙_ (Over S)).left) z (((O k).L.pull (eSec B)).U fun _ => i) ((O k).rig.s fun _ => i) = 1 := by
  obtain ⟨J, hJ, rfl⟩ := exists_good_at (O k).isLB z (eSec B) i hi
  have hq : eSec G ≫ q.left = eSec B := congrArg (·.left) (IsMonHom.one_hom q)
  have : cv O q u k _ (eSec G) z J * rv O k _ (𝟙 (𝟙_ (Over S)).left) z J = 1 := congrFun (congrFun (congrFun h k) z) ⟨J, hJ⟩
  unfold cv rv at this
  rw [hq, val_of _ _ z J (fun _ => J (eSec B)) fun _ => by rw [Category.id_comp]] at this
  exact this
end GlobalTheory.GeneratorLaw
