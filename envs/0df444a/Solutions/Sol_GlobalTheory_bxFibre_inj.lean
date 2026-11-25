-- Prove2me | solution 1 for GlobalTheory.bxFibre_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:43:50.429592+00:00
-- url     : https://prove2.me/submissions/81a52c5a-ac22-418a-af5e-585329024d21

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsFibreProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] {φ ψ : Γ(Y, U) →+* P}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) : φ = ψ := by
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
end GlobalTheory
