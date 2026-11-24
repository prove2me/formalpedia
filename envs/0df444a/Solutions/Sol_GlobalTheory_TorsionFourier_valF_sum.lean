-- Prove2me | solution 1 for GlobalTheory.TorsionFourier.valF_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:39:02.989326+00:00
-- url     : https://prove2.me/submissions/744cad26-3d86-450a-96f0-0be0eda6ed07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinsuppEqZeroOfSumTorsionCharactersEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PartVanishesOnTorusTorsionFourier

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
open GlobalTheory GlobalTheory.TorsionFourier
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens}
namespace GlobalTheory.TorsionFourier
theorem _root_.solution (h : ⊤ ≤ x ⁻¹ᵁ U) {J : Type} (A : Finset J) (a : J → Γ(X, U)) :
    valF x U (∑ j ∈ A, a j) = ∑ j ∈ A, valF x U (a j) := by
  simp only [valF, dif_pos h, map_sum]
end GlobalTheory.TorsionFourier
