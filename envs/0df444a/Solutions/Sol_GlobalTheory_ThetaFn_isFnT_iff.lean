-- Prove2me | solution 1 for GlobalTheory.ThetaFn.isFnT_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:33:54.817225+00:00
-- url     : https://prove2.me/submissions/f684255b-62c9-4679-8266-910934bb6237

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.ThetaFn
theorem _root_.solution (k : ℤ) (s : LB.Sec (LPow A L k (baseOver (Sp ℂ)))) (θ : (Fin g → ℂ) → ℂ) :
    IsFnT u k s θ ↔ ∀ (j : Fin 1 → L.ι) z, ⊤ ≤ exT u z ⁻¹ᵁ (LPow A L k (baseOver (Sp ℂ))).U j →
      valAt' (exT u z) ((LPow A L k (baseOver (Sp ℂ))).U j) (s.f j) = θ z * u.fr (j 0) z ^ k :=
  Iff.rfl
end GlobalTheory.ThetaFn
