-- Prove2me | solution 1 for GlobalTheory.TorsionIntegral.Restricts.isAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:04:47.425641+00:00
-- url     : https://prove2.me/submissions/e1995d3b-3488-44cd-9575-a375c5c3ccfa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_GlobalTheory_TorsionIntegral_corr_of_val_generic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub


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
open GlobalTheory
open GlobalTheory.TorsionIntegral
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (z : (TF (R := R) F).left)
variable (hd : ∀ (U : T.left.Opens) (y : T.left), y ∈ U → φ.left z ∈ U)
  (hi : ∀ (U : T.left.Opens), φ.left z ∈ U → Function.Injective (gm φ.left z U))
  (he : ∀ ψ ψ' : T.left ⟶ D.P.A.left, φ.left ≫ ψ = φ.left ≫ ψ' → ψ = ψ')
include hd hi he
namespace GlobalTheory.TorsionIntegral
namespace Restricts
theorem _root_.solution {g₁' g₂' g₃' : GtPt D T} {g₁ g₂ g₃ : GtPtF D F} (h₁ : Restricts φ z g₁' g₁)
    (h₂ : Restricts φ z g₂' g₂) (h₃ : Restricts φ z g₃' g₃) (h : g₁.IsAdd g₂ g₃) : g₁'.IsAdd g₂' g₃' := by
  obtain ⟨hb, hv⟩ := (isAdd_iff _ _ _).1 h
  have e : φ ≫ g₃'.b = φ ≫ (g₁'.b * g₂'.b) := by rw [MonObj.comp_mul, h₁.1, h₂.1, h₃.1, hb]
  refine ⟨Over.OverMorphism.ext (he _ _ (congrArg (fun q => q.left) e)),
    fun χ => corr_of_val_generic D.P.isLB φ.left z hd hi he fun J hJ => ?_⟩
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  rw [h₁.2 χ J hJ, h₂.2 χ J hJ, h₃.2 χ J hJ, ← hv χ z J hJ]
  refine congrArg _ ((val_cub D.cub φ hJ (cP D T χ) _ _).trans ?_)
  rw [comp_cP, h₁.1, h₂.1]
end Restricts
end GlobalTheory.TorsionIntegral
