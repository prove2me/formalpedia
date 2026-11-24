-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.eq_of_res_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:38:13.9348+00:00
-- url     : https://prove2.me/submissions/0fb2f798-47c1-41e4-8229-d9d65d48b699

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SteinOfBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge
variable {R : Type} [CommRing R] {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.Hodge
theorem _root_.solution (W : X.Opens) (a b : Γ(X, W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W),
      X.presheaf.map (homOfLE hV).op a = X.presheaf.map (homOfLE hV).op b) : a = b := by
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i : {V : X.affineOpens // V.1 ≤ W} => i.1.1) W
    (fun i => homOfLE i.2)
  · intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Scheme.isBasis_affineOpens X) hx
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    exact h i.1 i.2
end GlobalTheory.CompanionTheory.Hodge
