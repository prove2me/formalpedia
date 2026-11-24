-- Prove2me | solution 1 for GlobalTheory.ProjSpace.IsCoordFamily.toHom_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:09:29.045898+00:00
-- url     : https://prove2.me/submissions/c3875132-cdef-4ac9-ab05-88c431895e2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Theorems.Thm_GlobalTheory_ProjSpace_IsCoordFamily_exists_mem
import Theorems.Thm_GlobalTheory_ProjSpace_IsCoordFamily_pullRatio_toHom

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
theorem _root_.solution (f : Y ⟶ Sp R) (i : Fin (N + 1)) : H.toHom f ⁻¹ᵁ chart R N i = U i := by
  refine le_antisymm (fun y hy => ?_) (H.le_toHom_preimage f i)
  obtain ⟨k, hk⟩ := H.exists_mem y
  refine H.basicOpen_le k i ?_
  rw [← H.pullRatio_toHom f k i, basicOpen_pullRatio]
  exact ⟨hk, hy⟩
end GlobalTheory.ProjSpace.IsCoordFamily
