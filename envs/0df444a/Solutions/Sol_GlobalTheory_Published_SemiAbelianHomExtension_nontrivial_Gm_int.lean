-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.nontrivial_Gm_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:03.984529+00:00
-- url     : https://prove2.me/submissions/4463be48-a01b-4e60-9c60-3c6fa016cda4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
open scoped TensorProduct
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution : Nontrivial (𝟙_ (Over (Sp ℤ)) ⟶ Gm (Sp ℤ)) := by
  refine (splitTorusPointsEquiv (Sp ℤ) (ULift.{0} ℤ) (𝟙_ _)).toEquiv.nontrivial_congr.2 ?_
  refine ⟨(zpowersHom _ (-1)).comp (AddEquiv.toMultiplicative (AddEquiv.ulift (α := ℤ))).toMonoidHom, 1,
    fun h => ?_⟩
  have h₀ := DFunLike.congr_fun h (Multiplicative.ofAdd (ULift.up 1))
  change (-1 : Γ(Sp ℤ, ⊤)ˣ) ^ (1 : ℤ) = 1 at h₀
  rw [zpow_one] at h₀
  have h₁ : (-1 : Γ(Sp ℤ, ⊤)) = 1 := congrArg Units.val h₀
  have h₂ := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom h₁
  rw [map_neg, map_one] at h₂
  exact absurd h₂ (by decide : (-1 : ℤ) ≠ 1)
end GlobalTheory.Published.SemiAbelianHomExtension
