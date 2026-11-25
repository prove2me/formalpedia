-- Prove2me | solution 1 for GlobalTheory.LocLift.HasForm.of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:22.546284+00:00
-- url     : https://prove2.me/submissions/5093eed6-fff1-4c35-a69c-edfe9a182596

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
open Matrix
namespace GlobalTheory.LocLift
namespace HasForm
theorem _root_.solution {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La} {P : La → (Fin g → ℂ)} {g' : ℕ}
    (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hL : Function.Injective L) (h : HasForm EF (fun x => L (P x))) :
    HasForm EF P := by
  obtain ⟨Hm, h1, h2, h3⟩ := h
  let M := LinearMap.toMatrix' L
  have key : ∀ z w, hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec L z, ← LinearMap.toMatrix'_mulVec L w, hermForm, hermForm, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, star_mulVec, ← mulVec_transpose]
    rfl
  refine ⟨Mᵀ * Hm * Mᵀᴴ, isHermitian_mul_mul_conjTranspose _ h1, fun z hz => ?_, fun x y => ?_⟩
  · rw [key]
    exact h2 _ fun h0 => hz (hL (h0.trans (map_zero L).symm))
  · rw [key, h3]
end HasForm
end GlobalTheory.LocLift
