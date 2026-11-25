-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.pt_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:06:46.195633+00:00
-- url     : https://prove2.me/submissions/fa7bf506-48e8-4547-a9c3-8b121184b243

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
import Theorems.Thm_GlobalTheory_GeneratorLaw_gm_appLE
import Theorems.Thm_GlobalTheory_GeneratorLaw_exists_good_at
import Theorems.Thm_GlobalTheory_GenScheme_compat_pb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
theorem _root_.solution (hu : ∀ k, GenScheme.Compat (O k).L q.left (u k))
    (hU : GenScheme.Univ (fun k => (O k).L) q.left u) {W : Over S} (x y : W ⟶ G) (h₁ : x ≫ q = y ≫ q)
    (h₂ : nv O q u x = nv O q u y) : x = y := by
  have hq : x.left ≫ q.left = y.left ≫ q.left := congrArg (·.left) h₁
  refine Over.OverMorphism.ext ((hU W.left (y.left ≫ q.left) _
    fun k => GenScheme.compat_pb _ (hu k) y.left rfl).unique ⟨hq, fun k i => ?_⟩ ⟨rfl, fun k i => rfl⟩)
  refine congrArg Units.val (unit_ext fun z hz => ?_ : GenScheme.pb x.left _ _ _ (u k i) = _)
  obtain ⟨J, hJ, rfl⟩ := exists_good_at (O k).isLB z (y.left ≫ q.left) i hz
  refine (gm_appLE (𝟙 _) x.left z _ _ _ hz _).trans (Eq.trans ?_ (gm_appLE (𝟙 _) y.left z _ _ _ hz _).symm)
  rw [Category.id_comp, Category.id_comp]
  have := mul_right_cancel (congrFun (congrFun (congrFun h₂ k) z) ⟨J, hJ⟩)
  unfold cv at this
  rwa [hq] at this
end GlobalTheory.GeneratorLaw
