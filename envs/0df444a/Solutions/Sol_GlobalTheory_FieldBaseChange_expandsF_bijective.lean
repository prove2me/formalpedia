-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.expandsF_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:49.786991+00:00
-- url     : https://prove2.me/submissions/56cdba3a-b68b-43e4-8a1b-af7665cb6f77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Theorems.Thm_GlobalTheory_FieldBaseChange_isoRelM_bijective
import Theorems.Thm_GlobalTheory_FieldBaseChange_expandsG_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
variable {k : ℕ} {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))}
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (hG : GlobalFnsSt) (hk : 1 ≤ k) (h : U.ExpBij k) (hw : w.IsGen) :
    (∀ t, ∃! s, U.ExpandsF F k w t s) ∧ ∀ s, ∃! t, U.ExpandsF F k w t s := by
  obtain ⟨g₁, g₂⟩ := expandsG_bijective U F hG hk h
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  obtain ⟨i₁, i₂⟩ := isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')
  refine ⟨fun t => existsUnique_of_exists_of_unique ?_ ?_, fun s => existsUnique_of_exists_of_unique ?_ ?_⟩
  · obtain ⟨v, hv⟩ := (i₁ t).exists
    obtain ⟨s, hs⟩ := (g₁ v).exists
    exact ⟨s, v, hv, hs⟩
  · rintro s s' ⟨v, a, b⟩ ⟨v', a', b'⟩
    obtain rfl := (i₁ t).unique a a'
    exact (g₁ v).unique b b'
  · obtain ⟨v, hv⟩ := (g₂ s).exists
    obtain ⟨t, ht⟩ := (i₂ v).exists
    exact ⟨t, v, ht, hv⟩
  · rintro t t' ⟨v, a, b⟩ ⟨v', a', b'⟩
    obtain rfl := (g₂ s).unique b b'
    exact (i₂ v).unique a a'
end GlobalTheory.FieldBaseChange
