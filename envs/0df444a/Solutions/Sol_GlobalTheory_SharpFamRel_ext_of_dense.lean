-- Prove2me | solution 1 for GlobalTheory.SharpFamRel.ext_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:13:51.820959+00:00
-- url     : https://prove2.me/submissions/9d2922b5-1aac-438e-ac2e-2b0c7e3b6ea5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpFamRel
namespace GlobalTheory.SharpFamRel
theorem _root_.solution {S : Scheme.{0}} {T G : Over S} [IsReduced T.left] (hT : IsOpenMap T.hom) [IsSeparated G.hom]
    (f g : T ⟶ G) {D : Set S} (hD : Dense D)
    (H : ∀ p ∈ D, ∃ (Z Y : Scheme.{0}) (ψ : Z ⟶ T.left) (q : Z ⟶ Y) (x : Y ⟶ S), IsPullback ψ q T.hom x ∧
      p ∈ Set.range x ∧ ψ ≫ f.left = ψ ≫ g.left) : f = g := by
  choose Z Y ψ q x hpb hx hψ using H
  let inc : (∐ fun p : D => Z p.1 p.2) ⟶ T.left := Sigma.desc fun p => ψ p.1 p.2
  have hinc : inc ≫ f.left = inc ≫ g.left := by
    refine Sigma.hom_ext _ _ fun p => ?_
    simp only [inc, Sigma.ι_desc_assoc]
    exact hψ p.1 p.2
  have hsub : T.hom.base ⁻¹' D ⊆ Set.range inc.base := by
    intro a ha
    obtain ⟨y, hy⟩ := hx _ ha
    obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback a y hy.symm
    refine ⟨(Sigma.ι (fun p : D => Z p.1 p.2) ⟨_, ha⟩).base ((hpb _ ha).isoPullback.inv.base z), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
    show ((hpb _ ha).isoPullback.inv ≫ ψ _ ha) z = a
    rw [IsPullback.isoPullback_inv_fst]
    exact hz₁
  have : IsDominant inc := ⟨((hD.preimage hT).mono hsub)⟩
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w f, Over.w g]) inc hinc)
end GlobalTheory.SharpFamRel
