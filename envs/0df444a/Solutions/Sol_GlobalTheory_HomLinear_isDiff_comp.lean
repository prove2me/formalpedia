-- Prove2me | solution 1 for GlobalTheory.HomLinear.isDiff_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:35.212811+00:00
-- url     : https://prove2.me/submissions/e950d953-ab02-4176-8641-ac0736c9cb06

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Theorems.Thm_P2M_GlobalTheory_HomLinear_valAt__comp_left_59bd74891c19
import Theorems.Thm_GlobalTheory_HomLinear_isTangent_comp
import Theorems.Thm_GlobalTheory_HomLinear_top_le_ex_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HomLinear
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
namespace GlobalTheory.HomLinear
theorem _root_.solution (u : HolUnif A L g) (u' : HolUnif A' L' g') (f : A ⟶ A') [IsMonHom f]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hd : u.IsDiff w v) : u'.IsDiff (F w) (v ≫ f) := by
  intro U h s
  have h1 := hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)
  have e : ((v ≫ f).left.appLE U ⊤ h).hom s =
      (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s) := by
    have := Scheme.Hom.comp_appLE v.left f.left U ⊤ h
    exact congrArg (fun φ => φ.hom s) this
  have hdiff : DifferentiableAt ℂ (fun z => valAt' (u'.ex z).left U s) 0 :=
    (u'.hol U s).2.differentiableAt ((u'.hol U s).1.mem_nhds (top_le_ex_zero u' (isTangent_comp f hv) U h))
  have hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) =
      (fun z => valAt' (u'.ex z).left U s) ∘ LinearMap.toContinuousLinearMap F := by
    funext z
    rw [← valAt'_comp_left, ← hF]
    rfl
  have hch := (HasFDerivAt.comp (0 : Fin g → ℂ) (f := LinearMap.toContinuousLinearMap F)
    (by rw [map_zero]; exact hdiff.hasFDerivAt) (LinearMap.toContinuousLinearMap F).hasFDerivAt).fderiv
  rw [hfun, hch] at h1
  rw [e]
  exact h1
end GlobalTheory.HomLinear
