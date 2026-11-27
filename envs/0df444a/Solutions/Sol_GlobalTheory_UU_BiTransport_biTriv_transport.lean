-- Prove2me | solution 1 for GlobalTheory.UU.BiTransport.biTriv_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:35.910401+00:00
-- url     : https://prove2.me/submissions/d5c280d7-b424-498f-86ce-1df3d94f7fee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BiTrivTransport
import Theorems.Thm_GlobalTheory_UU_BiTransport_exists_transport
import Theorems.Thm_GlobalTheory_SplitTorus_isGrpPullback_bcMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiTransport
variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}
namespace GlobalTheory.UU.BiTransport
theorem _root_.solution : ∀ (S S₀ : Scheme.{0}) (ρ : S₀ ⟶ S) [Mono ρ] (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G ρ F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P ρ F hw w → ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat ρ F i₀ i → BiTriv P₀.c i₀ → ∃ s : LB.Gen (LB.LinComb P.L.L (fun k => pullback.fst (splitTorus S X ⊗ G).hom ρ ≫ lamφ i k) Oε), s.IsGen ∧ (∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (x : Z ⟶ G) (a b d : Z.left ⟶ pullback (splitTorus S X ⊗ G).hom ρ), a ≫ pullback.fst _ _ = (lift (t * t') x).left → b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t' x).left → ∀ (z : Z.left) (I), Good P.L.L z I → val s a z I = cubV P.c z I (t ≫ i) (t' ≫ i) x * val s b z I * val s d z I) ∧ (∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x x' : Z ⟶ G) (a b d : Z.left ⟶ pullback (splitTorus S X ⊗ G).hom ρ), a ≫ pullback.fst _ _ = (lift t (x * x')).left → b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t x').left → ∀ (z : Z.left) (I), Good P.L.L z I → val s a z I = cubV P.c z I (t ≫ i) x x' * val s b z I * val s d z I) := by
  intro S S₀ ρ _ X _ G _ _ G₀ _ _ F hw hF P P₀ w hP i i₀ _ _ hi σ
  exact exists_transport hF.1 (SplitTorus.isGrpPullback_bcMap ρ X) hP (torusCompat_iff.1 hi) σ
end GlobalTheory.UU.BiTransport
