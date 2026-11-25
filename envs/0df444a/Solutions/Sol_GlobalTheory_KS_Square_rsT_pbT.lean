-- Prove2me | solution 1 for GlobalTheory.KS.Square.rsT_pbT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:38:34.831746+00:00
-- url     : https://prove2.me/submissions/82225440-3109-4bec-8231-2839ff660a92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCoversStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsSymmOfSquare
import Theorems.Thm_GlobalTheory_KS_Square_rsT_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Square
variable {Z : Scheme.{0}}
namespace GlobalTheory.KS.Square
theorem _root_.solution {Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O O' : Z.Opens} (h' : O' ≤ O)
    (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) : rsT (pbT f s O) O' = pbT f s O' := by
  unfold pbT
  rw [dif_pos h, dif_pos (h'.trans h), rsT_eq h']
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
end GlobalTheory.KS.Square
