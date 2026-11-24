-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.exists_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:48:57.820824+00:00
-- url     : https://prove2.me/submissions/09535168-5250-4dc0-8638-27baf16c4855

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SteinOfBijective
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_eq_of_res_affine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.Hodge
variable {R : Type} [CommRing R] {X : Scheme.{0}}
private theorem res_res_lemma {A B C : X.Opens} (f : B ⟶ A) (g' : C ⟶ B) (s : Γ(X, A)) :
    X.presheaf.map g'.op (X.presheaf.map f.op s) = X.presheaf.map (g' ≫ f).op s := by
  rw [op_comp, Functor.map_comp]
  rfl
end GlobalTheory.CompanionTheory.Hodge
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge
variable {R : Type} [CommRing R] {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.Hodge
theorem _root_.solution (g : ∀ U : X.affineOpens, Γ(X, U.1))
    (hg : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1), X.presheaf.map (homOfLE h).op (g U) = g V) :
    ∃ t : Γ(X, ⊤), ∀ U : X.affineOpens,
      X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op t = g U := by
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun i : X.affineOpens => i.1) g := by
    intro i j
    apply eq_of_res_affine
    intro V hV
    rw [res_res_lemma, res_res_lemma]
    exact (hg i V (hV.trans inf_le_left)).trans (hg j V (hV.trans inf_le_right)).symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i : X.affineOpens => i.1) ⊤
    (fun i => homOfLE le_top) (by
      intro x _
      obtain ⟨V, hV, hxV, -⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X)
          (show x ∈ (⊤ : X.Opens) from trivial)
      rw [TopologicalSpace.Opens.mem_iSup]
      exact ⟨⟨V, hV⟩, hxV⟩) g hcompat
  exact ⟨t, ht⟩
end GlobalTheory.CompanionTheory.Hodge
