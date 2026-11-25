-- Prove2me | solution 1 for GlobalTheory.ProjSpace.IsCoordFamily.toHom_str
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:06:51.623325+00:00
-- url     : https://prove2.me/submissions/b5ffa586-f695-48d6-9651-9322eaabc872

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Theorems.Thm_GlobalTheory_ProjSpace_IsCoordFamily_exists_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG)
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable {R : Type} [CommRing R] {N : ℕ} {Y Z : Scheme.{0}}
open GlobalTheory.ProjSpace.IsCoordFamily
variable {U : Fin (N + 1) → Y.Opens} {r : ∀ i, Fin (N + 1) → Γ(Y, U i)} (H : IsCoordFamily U r)
include H
namespace GlobalTheory.ProjSpace.IsCoordFamily
theorem _root_.solution (f : Y ⟶ Sp R) : H.toHom f ≫ PSpace.str R N = f := by
  refine Scheme.hom_ext_of_forall _ _ fun y => ?_
  obtain ⟨i, hi⟩ := H.exists_mem y
  exact ⟨U i, hi, by rw [← Category.assoc, ι_toHom, ofCoords_str]⟩
end GlobalTheory.ProjSpace.IsCoordFamily
