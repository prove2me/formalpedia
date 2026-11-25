-- Prove2me | solution 1 for GlobalTheory.CubTrivTorus.cubTriv_delta_and_even_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:30.319582+00:00
-- url     : https://prove2.me/submissions/9532d6b5-332a-43c6-892a-327973c69091

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Theorems.Thm_GlobalTheory_CubTrivTorus_val_mul_eq
import Theorems.Thm_GlobalTheory_CubTrivTorus_eq_of_even

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
noncomputable section
open GlobalTheory GlobalTheory.CubTrivTorus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable [ConnectedSpace S] [Module.Free ℤ X] {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G}
  [IsMonHom i]
namespace GlobalTheory.CubTrivTorus
theorem _root_.solution : (∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G] (P : CP G) (i : splitTorus S X ⟶ G), IsMonHom i → (∀ (s : BiTriv P.c i) (σ : CubTriv P.c i) (T : Over S) (t t' : T ⟶ splitTorus S X) (z : T.left) (J), Good P.L.L z J → val σ.s (t * t').left z J = val s.s (lift t (t' ≫ i)).left z J * val σ.s t.left z J * val σ.s t'.left z J) ∧ ∀ σ σ' : CubTriv P.c i, σ.Even → σ'.Even → σ = σ') := by
  intro S _ X _ _ G _ _ P i hi
  exact ⟨fun s σ T t t' z J hJ => val_mul_eq s σ T t t' z J hJ, fun σ σ' h h' => eq_of_even h h'⟩
end GlobalTheory.CubTrivTorus
