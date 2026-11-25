-- Prove2me | solution 1 for GlobalTheory.CubTrivTorus.val_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:46:36.826834+00:00
-- url     : https://prove2.me/submissions/704d3399-5bc1-499b-abb3-ee62187a370c

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
import Theorems.Thm_GlobalTheory_CubTrivTorus_eq_one_of_mul
import Theorems.Thm_GlobalTheory_CubTrivTorus_connectedSpace_torus
import Theorems.Thm_GlobalTheory_CubTrivTorus_exists_unit_delta
import Theorems.Thm_GlobalTheory_UU_BiTriv_val_one_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
theorem _root_.solution {L : RigLB G} {c : CubicalStr G L} (s : BiTriv c i) (σ : CubTriv c i) (T : Over S)
    (t t' : T ⟶ splitTorus S X) (z : T.left) (J) (hJ : Good L.L z J) : val σ.s (t * t').left z J =
      val s.s (lift t (t' ≫ i)).left z J * val σ.s t.left z J * val σ.s t'.left z J := by
  haveI : ConnectedSpace (splitTorus S X).left := connectedSpace_torus
  obtain ⟨a, ha⟩ := exists_unit_delta s σ
  have hmul : ∀ (Z : Over S) (t₁ t₂ y : Z ⟶ splitTorus S X) (z : Z.left),
      gm (lift (t₁ * t₂) y).left z ⊤ a = gm (lift t₁ y).left z ⊤ a * gm (lift t₂ y).left z ⊤ a := by
    intro Z t₁ t₂ y z
    obtain ⟨J, hJ⟩ := exists_good_pt L.isLB z
    have h1 := ha Z (t₁ * t₂) y z J hJ
    have h2 := ha Z t₁ y z J hJ
    have h3 := ha Z t₂ y z J hJ
    have hc := σ.cub Z t₁ t₂ y z J hJ
    have hl := s.law1 Z t₁ t₂ (y ≫ i) z J hJ
    have alg : ∀ A A₁ A₂ C s₁ s₂ P Q R Y : (Z.left.presheaf.stalk z)ˣ,
        A * (C * s₁ * s₂ * P * Y) * Q * R * Y = C * P * (A₁ * (s₁ * Q * Y)) * (A₂ * (s₂ * R * Y)) → A = A₁ * A₂ := by
      intro A A₁ A₂ C s₁ s₂ P Q R Y h
      apply mul_right_cancel (b := C * s₁ * s₂ * P * Y * Q * R * Y)
      calc A * (C * s₁ * s₂ * P * Y * Q * R * Y) = A * (C * s₁ * s₂ * P * Y) * Q * R * Y := by ac_rfl
        _ = C * P * (A₁ * (s₁ * Q * Y)) * (A₂ * (s₂ * R * Y)) := h
        _ = A₁ * A₂ * (C * s₁ * s₂ * P * Y * Q * R * Y) := by ac_rfl
    rw [h1, h2, h3, hl] at hc
    exact alg _ _ _ _ _ _ _ _ _ _ hc
  have hone : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left),
      gm (lift t (1 : Z ⟶ splitTorus S X)).left z ⊤ a = 1 := by
    intro Z t z
    obtain ⟨J, hJ⟩ := exists_good_pt L.isLB z
    have h1 := ha Z t 1 z J hJ
    rw [_root_.mul_one, MonObj.one_comp, BiTriv.val_one_right s hJ, CubTriv.val_one σ hJ, _root_.one_mul,
      _root_.mul_one] at h1
    calc _ = gm (lift t (1 : Z ⟶ splitTorus S X)).left z ⊤ a * val σ.s t.left z J * (val σ.s t.left z J)⁻¹ := by group
      _ = 1 := by rw [← h1, _root_.mul_inv_cancel]
  rw [ha T t t' z J hJ, eq_one_of_mul a hmul hone T t t' z, _root_.one_mul]
end GlobalTheory.CubTrivTorus
