-- Prove2me | solution 1 for GlobalTheory.SecAff.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:34.635153+00:00
-- url     : https://prove2.me/submissions/527a953c-7ffe-45f6-934b-efcfec1e4162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
namespace GlobalTheory.SecAff
theorem _root_.solution (h : T' ⟶ T) (V : T.left.Opens) (hV : ∀ x, h.left x ∈ V) :
    ∃ k : T' ⟶ overRes V, k ≫ overResι V = h := by
  have hr : Set.range h.left ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨_, hV x⟩, rfl⟩
  refine ⟨Over.homMk (IsOpenImmersion.lift V.ι h.left hr) ?_, ?_⟩
  · change _ ≫ V.ι ≫ T.hom = T'.hom
    rw [IsOpenImmersion.lift_fac_assoc, Over.w h]
  · ext1
    exact IsOpenImmersion.lift_fac V.ι h.left hr
end GlobalTheory.SecAff
