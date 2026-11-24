-- Prove2me | solution 1 for GlobalTheory.ToSplit.exists_gen_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:21:53.048359+00:00
-- url     : https://prove2.me/submissions/5758deaf-d8f7-42bd-8307-2dd5663dd5f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Theorems.Thm_P2M_GlobalTheory_ToSplit_gm_id_pull__a5960ce669d6
import Theorems.Thm_GlobalTheory_ToSplit_unit_ext_of_cover
import Theorems.Thm_GlobalTheory_ToSplit_exists_unit_descent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {X Y : Over S} (π : Y ⟶ X) [Flat π.left] [Surjective π.left]
  [QuasiCompact π.left]
namespace GlobalTheory.ToSplit
theorem _root_.solution (M : LB X.left) (f : ∀ j, Γ(Y.left, π.left ⁻¹ᵁ M.U j)ˣ)
    (hf : ∀ j (Z : Over S) (g₁ g₂ : Z ⟶ Y) (z : Z.left), g₁ ≫ π = g₂ ≫ π →
      π.left (g₁.left z) ∈ M.U j → π.left (g₂.left z) ∈ M.U j →
      gm g₁.left z _ (f j) = gm g₂.left z _ (f j))
    (hg : ∀ j j' (y : Y.left), π.left y ∈ M.U j → π.left y ∈ M.U j' →
      gm (𝟙 _) y _ (f j) = gm π.left y (M.U j ⊓ M.U j') (M.g j j') * gm (𝟙 _) y _ (f j')) :
    ∃ t : LB.Gen M, t.IsGen := by
  choose a ha using fun j => exists_unit_descent π (M.U j) (f j) (hf j)
  refine ⟨⟨a⟩, fun j j' => unit_ext_of_cover π.left fun y hy => ?_⟩
  rw [map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy, ← gm_id_pull' π.left y hy.1 (a j),
    ← gm_id_pull' π.left y hy.2 (a j'), ha, ha]
  exact hg j j' y hy.1 hy.2
end GlobalTheory.ToSplit
