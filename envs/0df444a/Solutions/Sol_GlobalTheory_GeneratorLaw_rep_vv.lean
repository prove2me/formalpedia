-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.rep_vv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:51:44.197354+00:00
-- url     : https://prove2.me/submissions/a5c4fcc7-1afa-4abb-84b6-f9aeedd5cea8

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
import Theorems.Thm_GlobalTheory_GeneratorLaw_Rep_congr
import Theorems.Thm_GlobalTheory_PrimCocycle_prod_lam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {κ : Type} (O : κ → RigLB B) {G : Over S} (q : G ⟶ B)
  (u : ∀ k (i : (O k).L.ι), Γ(G.left, q.left ⁻¹ᵁ (O k).L.U i)ˣ)
variable {O q u}
variable [IsCommMonObj B] (t : ∀ k, LB.Gen (abelian₂ B (O k).L))
variable {t}
namespace GlobalTheory.GeneratorLaw
theorem _root_.solution (ht : ∀ k, (t k).IsGen) (k : κ) {Y : Over S} (x y : Y ⟶ B) :
    Rep (O k).L (fun _ _ h => h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : Y ⟶ B).left)
      (fun _ r z J => val (L := (O k).L) (φ := PrimCocycle.lamφ B) (ε := PrimCocycle.lamε) (t k)
        (r ≫ (lift x y).left) z J) :=
  (Rep.pull (σ := fun _ _ h => ∏ I, h (PrimCocycle.lamφ B I) ^ PrimCocycle.lamε I)
    ⟨_, inferInstance, _, _, t k, ht k, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩ (lift x y).left).congr
    fun _ _ h => PrimCocycle.prod_lam x y h
end GlobalTheory.GeneratorLaw
