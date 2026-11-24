-- Prove2me | solution 1 for GlobalTheory.ZM.IntegersAway.isPrimitiveRoot_map_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:57.940383+00:00
-- url     : https://prove2.me/submissions/862abf0f-8999-40cd-be3e-6684d500749f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPrimitiveRootMapOfNatCastNeZero

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.IntegersAway
namespace GlobalTheory.ZM.IntegersAway
theorem _root_.solution {R K : Type} [CommRing R] [IsDomain R] [CharZero R] [Field K] {k : ℕ}
    (hk : 0 < k) {z : R} (hz : IsPrimitiveRoot z k) (β : R →+* K) (hβ : (k : K) ≠ 0) : IsPrimitiveRoot (β z) k := by
  have : NeZero (k : K) := ⟨hβ⟩
  have h : (Polynomial.cyclotomic k R).IsRoot z := hz.isRoot_cyclotomic hk
  rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic k β]
  exact h.map
end GlobalTheory.ZM.IntegersAway
