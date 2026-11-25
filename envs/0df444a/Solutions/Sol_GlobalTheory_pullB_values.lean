-- Prove2me | solution 1 for GlobalTheory.pullB_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:29:36.989565+00:00
-- url     : https://prove2.me/submissions/1997ef19-ac91-465c-bd78-9457d3b29b23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PullBValues
import Theorems.Thm_GlobalTheory_values_natural
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T₀ : Over (Spec (CommRingCat.of R))) (φ : TF (R := R) F ⟶ T₀) (k : ℕ) (f : ∀ α, SecBT D T₀ k α) (s : Raw D F k), PullB D F φ k f s → ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ TF (R := R) F) (x : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval (s α) (lift ρ x).left z J = sval (f α) (lift (ρ ≫ φ) x).left z J := by
  intro R _ _ D F _ _ T₀ φ k f s h α T ρ x z J hJ
  have e : (lift ρ x).left ≫ (φ ▷ D.P.A).left = (lift (ρ ≫ φ) x).left := by
    rw [← Over.comp_left, lift_whiskerRight]
  have a := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (𝟙 (DegPre.BF D F).left) (lift ρ x).left z J hJ).2.1 (s α)
  have b := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (φ ▷ D.P.A).left (lift ρ x).left z J hJ).2.1 (f α)
  have hJ' : Good D.P.L ((lift ρ x).left z) (fun ψ => J ((lift ρ x).left ≫ ψ)) := fun ψ => hJ _
  rw [e] at b
  rw [Category.comp_id] at a
  exact a.trans ((congrArg _ (h α _ _ hJ')).trans b.symm)
end GlobalTheory
