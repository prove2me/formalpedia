-- Prove2me | solution 1 for GlobalTheory.SecAff.whisker_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:49.406255+00:00
-- url     : https://prove2.me/submissions/25054e41-36d6-446f-9fb6-43097fb3f401

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_isPullback_whisker

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
omit [GrpObj A]
namespace GlobalTheory.SecAff
theorem _root_.solution (h : T' ⟶ T) [IsOpenImmersion h.left] [IsOpenImmersion (h ▷ A).left]
    (r : Γ(T.left, ⊤)) (hr : h.left.opensRange = T.left.basicOpen r) :
    (h ▷ A).left.opensRange =
      (T ⊗ A).left.basicOpen (pa (fst T A).left (V := ⊤) (le_pre_top _) r) := by
  have e : (T ⊗ A).left.basicOpen (pa (fst T A).left (V := ⊤) (le_pre_top _) r) =
      (fst T A).left ⁻¹ᵁ T.left.basicOpen r := by
    have := Scheme.basicOpen_appLE (fst T A).left ⊤ ⊤ (le_pre_top _) r
    rw [top_inf_eq] at this
    exact this
  rw [e, ← hr]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(fst T' A).left y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, whisker_fst_left]
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_whisker A h) x y hy.symm
    exact ⟨z, hz⟩
end GlobalTheory.SecAff
