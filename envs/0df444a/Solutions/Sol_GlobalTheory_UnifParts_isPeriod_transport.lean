-- Prove2me | solution 1 for GlobalTheory.UnifParts.isPeriod_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:48:21.47387+00:00
-- url     : https://prove2.me/submissions/2c812d53-1f9f-4956-880b-718ab8e2e6d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FamilyUnifOfParts

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
open GlobalTheory GlobalTheory.UnifParts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.UnifParts
theorem _root_.solution {D' D'' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (gam : D'.La ≃ₗ[𝓞 E] D''.La)
    (hgam : ∀ a b, D''.EF (gam a) (gam b) = D'.EF a b) {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ty P) :
    IsPeriod D'' ty (P.comp gam.symm.toLinearMap.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hP
  have hr : (P.comp gam.symm.toLinearMap.toAddMonoidHom).range = P.range := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨gam.symm a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨gam a, by simp⟩
  refine ⟨fun a x i => ?_, h2.comp gam.symm.injective, by rw [hr]; exact h3, ?_, Hm, h5, h6, fun x y => ?_⟩
  · simpa using h1 a (gam.symm x) i
  · rw [← h4, ← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
  · have := hgam (gam.symm x) (gam.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    rw [this, ← h7]; rfl
end GlobalTheory.UnifParts
