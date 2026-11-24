-- Prove2me | solution 1 for GlobalTheory.SecRatio.ratio_and_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:27.147058+00:00
-- url     : https://prove2.me/submissions/ec9bacb5-8067-47af-91bc-da9e236ae343

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Theorems.Thm_GlobalTheory_SecRatio_existsUnique_isRatio
import Theorems.Thm_GlobalTheory_SecRatio_existsUnique_isLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.SecRatio
variable {X : Scheme.{0}} {H : LB X}
namespace GlobalTheory.SecRatio
theorem _root_.solution : (∀ (X : Scheme.{0}) (H : LB X), H.IsLB → (∀ (s t : H.Sec) (W : X.Opens), W ≤ Out.nonzeroLocus t → ∃! r : Γ(X, W), IsRatio s t W r) ∧ ∀ (k : Type) [CommRing k] (p : X ⟶ Sp k) (J : Type) [Fintype J] (s : J → H.Sec) (a : J → k), ∃! φ : H.Sec, IsLin p s a φ) :=
  fun _ _ hH => ⟨existsUnique_isRatio hH, fun _ _ p _ _ s a => existsUnique_isLin p s a⟩
end GlobalTheory.SecRatio
