-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.exists_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:31:52.349515+00:00
-- url     : https://prove2.me/submissions/e6584566-9284-4d56-b3fa-468bfcc3e047

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
import Theorems.Thm_GlobalTheory_GeneratorLaw_Rep_mul
import Theorems.Thm_GlobalTheory_GeneratorLaw_Rep_inv
import Theorems.Thm_GlobalTheory_GeneratorLaw_Rep_congr
import Theorems.Thm_GlobalTheory_GeneratorLaw_rep_rv
import Theorems.Thm_GlobalTheory_GeneratorLaw_nv_comp
import Theorems.Thm_GlobalTheory_GeneratorLaw_exists_hom
import Theorems.Thm_GlobalTheory_GenScheme_exists_hom
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
namespace GlobalTheory.GeneratorLaw
theorem _root_.solution (hU : GenScheme.Univ (fun k => (O k).L) q.left u) {Y : Over S} (b : Y ⟶ B)
    (F : ∀ k, Vals (O k).L Y.left)
    (h : ∀ k, Rep (O k).L (fun _ _ h => (h b.left)⁻¹ * h (1 : Y ⟶ B).left) (F k)) :
    ∃ g : Y ⟶ G, g ≫ q = b ∧
      ∀ (W : Over S) (r : W ⟶ Y) k z J, nv O q u (r ≫ g) k z J = F k _ r.left z J.1 := by
  have H : ∀ k, Rep (O k).L (fun _ _ h => (h b.left)⁻¹)
      (fun Z r z J => F k Z r z J * (rv O k Z (r ≫ Y.hom) z J)⁻¹) :=
    fun k => ((h k).mul (rep_rv O k Y).inv).congr fun V _ h => mul_inv_cancel_right _ _
  obtain ⟨g, hg, hv⟩ := exists_hom (fun k => (O k).isLB) hU b.left _ H
  have w : g ≫ G.hom = Y.hom := by rw [← Over.w q, reassoc_of% hg, Over.w b]
  refine ⟨Over.homMk g w, Over.OverMorphism.ext hg, fun W r k z J => ?_⟩
  rw [← nv_comp, ← eq_mul_inv_iff_mul_eq]
  exact hv k _ r.left z J.1 J.2
end GlobalTheory.GeneratorLaw
