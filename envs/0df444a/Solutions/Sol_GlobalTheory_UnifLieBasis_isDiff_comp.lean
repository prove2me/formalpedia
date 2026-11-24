-- Prove2me | solution 1 for GlobalTheory.UnifLieBasis.isDiff_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:08.866146+00:00
-- url     : https://prove2.me/submissions/edb79cd0-c9a5-45c0-8cbf-65e0b59ef260

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLieBasisOfHolUnif
import Theorems.Thm_GlobalTheory_UnifLieBasis_isTangent_comp
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_mem_iff
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UnifLieBasis
open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.UnifLieBasis
theorem _root_.solution (f : A ⟶ A) [IsMonHom f] (F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hd : u.IsDiff w v) : u.IsDiff (F w) (v ≫ f) := by
  intro U h s
  have h1 := hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)
  have e : ((v ≫ f).left.appLE U ⊤ h).hom s =
      (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s) := by
    have := Scheme.Hom.comp_appLE v.left f.left U ⊤ h
    exact congrArg (fun φ => φ.hom s) this
  have hdiff := differentiableAt_val u ((tangent_mem_iff (u := u) (isTangent_comp f hv) U).1 h) s
  have hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) =
      (fun z => valAt' (u.ex z).left U s) ∘ F := by
    funext z
    rw [valAt'_comp, Function.comp_apply, hF]
    rfl
  have hch := (HasFDerivAt.comp (0 : Fin g → ℂ) (f := F)
    (by rw [map_zero]; exact hdiff.hasFDerivAt) F.hasFDerivAt).fderiv
  rw [hfun, hch] at h1
  rw [e]
  exact h1
end GlobalTheory.UnifLieBasis
