-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.exists_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:57:14.485022+00:00
-- url     : https://prove2.me/submissions/a1905cd4-78cc-4916-8e6c-f88a3b2c438a

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
import Theorems.Thm_GlobalTheory_GeneratorLaw_rep_nv
import Theorems.Thm_GlobalTheory_GeneratorLaw_nv_comp
import Theorems.Thm_GlobalTheory_GeneratorLaw_exists_pt
import Theorems.Thm_GlobalTheory_GeneratorLaw_rep_vv
import Theorems.Thm_GlobalTheory_GeneratorLaw_vv_comp
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
theorem _root_.solution (hu : ∀ k, GenScheme.Compat (O k).L q.left (u k))
    (hU : GenScheme.Univ (fun k => (O k).L) q.left u) (ht : ∀ k, (t k).IsGen) :
    ∃ m : G ⊗ G ⟶ G, ∀ (W : Over S) (x y : W ⟶ G), (lift x y ≫ m) ≫ q = (x ≫ q) * (y ≫ q) ∧
      nv O q u (lift x y ≫ m) = nv O q u x * nv O q u y * (vv t (x ≫ q) (y ≫ q))⁻¹ := by
  obtain ⟨m, h₁, h₂⟩ := exists_pt hU ((fst G G ≫ q) * (snd G G ≫ q)) _ fun k =>
    (((rep_nv hu k (fst G G)).mul (rep_nv hu k (snd G G))).mul
      (rep_vv ht k (fst G G ≫ q) (snd G G ≫ q)).inv).congr fun V _ h => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  refine ⟨m, fun W x y => ⟨?_, funext₃ fun k z J => ?_⟩⟩
  · rw [Category.assoc, h₁, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  · rw [h₂, nv_comp, nv_comp, vv_comp, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]; rfl
end GlobalTheory.GeneratorLaw
