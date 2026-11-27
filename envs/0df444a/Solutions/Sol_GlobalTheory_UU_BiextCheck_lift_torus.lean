-- Prove2me | solution 1 for GlobalTheory.UU.BiextCheck.lift_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:38.796945+00:00
-- url     : https://prove2.me/submissions/309164e3-7a04-481d-8649-398dcd3da1e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Statements_LocalTrivialization_ConnectedSpaceTorus
import Theorems.Thm_GlobalTheory_SplitTorus_connectedSpace_of_isLocalRing
import Theorems.Thm_GlobalTheory_SplitTorus_connectedSpace_quotient
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
noncomputable section
open GlobalTheory GlobalTheory.UU
open GlobalTheory.UU.BiextCheck
open SplitTorus (bcMap bcMap_hom)
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU.BiextCheck
theorem _root_.solution (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] (ψ : X) :
    ConnectedSpace (splitTorus (Spec (CommRingCat.of (A ⧸ J))) X).left ∧
    IsGrpPullback (splitTorus _ X) (splitTorus _ X) (red J) (bcMap (red J) X) ∧
    (∃ w, IsCPMap (twCP _ (-(ψ + ψ))) (twCP _ (-(ψ + ψ))) (red J) (bcMap (red J) X) (bcMap_hom _ X) w) ∧
    TorusCompat (red J) (bcMap (red J) X) (𝟙 _) (𝟙 _) ∧
    Nonempty (BiTriv (twCP (Spec (CommRingCat.of (A ⧸ J))) (-(ψ + ψ))).c (𝟙 _)) ∧
    Nonempty (BiTriv (twCP (Spec (CommRingCat.of A)) (-(ψ + ψ))).c (𝟙 _)) ∧
    (∃ σ₀ : CubTriv (twCP (Spec (CommRingCat.of (A ⧸ J))) (-(ψ + ψ))).c (𝟙 _), σ₀.Even) ∧
    ∃ σ : CubTriv (twCP (Spec (CommRingCat.of A)) (-(ψ + ψ))).c (𝟙 _), σ.Even := by
  have := SplitTorus.connectedSpace_of_isLocalRing A
  have : ConnectedSpace (Spec (CommRingCat.of (A ⧸ J))) := SplitTorus.connectedSpace_quotient J fun x hx => by
    obtain ⟨n, hn⟩ := hJ
    exact ⟨n, Ideal.mem_bot.1 (hn ▸ Ideal.pow_mem_pow hx n :)⟩
  exact ⟨connectedSpace_torus _ _, SplitTorus.isGrpPullback_bcMap _ _, ⟨_, isCPMap_bcMap _ _⟩, torusCompat_bcMap _,
    ⟨BiTriv.triv _⟩, ⟨BiTriv.triv _⟩, ⟨_, twTriv_even _ ψ⟩, ⟨_, twTriv_even _ ψ⟩⟩
end GlobalTheory.UU.BiextCheck
