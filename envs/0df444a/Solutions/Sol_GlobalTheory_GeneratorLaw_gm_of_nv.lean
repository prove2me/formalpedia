-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.gm_of_nv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:09:06.376991+00:00
-- url     : https://prove2.me/submissions/530a0507-0f1b-4503-9f60-e4f03a050087

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
omit [GrpObj G]
namespace GlobalTheory.GeneratorLaw
theorem _root_.solution {W : Over S} {g g' : W ⟶ G} {c : PV O W} (h₁ : g' ≫ q = g ≫ q)
    (h₂ : nv O q u g' = c * nv O q u g) (k : κ) (z : W.left) (i : (O k).L.ι)
    (hi : q.left (g.left z) ∈ (O k).L.U i) : ∃ J, gm g'.left z (q.left ⁻¹ᵁ (O k).L.U i) (u k i) =
      c k z J * gm g.left z (q.left ⁻¹ᵁ (O k).L.U i) (u k i) := by
  obtain ⟨J, hJ, rfl⟩ := exists_good_at (O k).isLB z (g.left ≫ q.left) i hi
  have hq : g'.left ≫ q.left = g.left ≫ q.left := congrArg (·.left) h₁
  have := mul_right_cancel ((congrFun (congrFun (congrFun h₂ k) z) ⟨J, hJ⟩).trans (_root_.mul_assoc _ _ _).symm)
  unfold cv at this
  rw [hq] at this
  exact ⟨⟨J, hJ⟩, this⟩
end GlobalTheory.GeneratorLaw
