-- Prove2me | solution 1 for GlobalTheory.SS.Ord.hasOrd_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:41:04.885559+00:00
-- url     : https://prove2.me/submissions/08b3df38-eede-4b71-8d07-3163a1d243f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_j_cst
import Theorems.Thm_GlobalTheory_SS_Ord_not_isUnit_cst
import Theorems.Thm_GlobalTheory_SS_Ord_j_app_injective

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.Ord
theorem _root_.solution [IsDomain R] [IsLocalRing R] [IsFractionRing R K] {I : Type} [Fintype I] [DecidableEq I]
    (M : Model R A) (D : I → VF A) {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) (h0 : π ≠ 0) {n m : ℤ}
    (hn : HasOrd M D π n) (hm : HasOrd M D π m) : n = m := by
  have key : ∀ {n m : ℤ}, HasOrd M D π n → HasOrd M D π m → ¬ n < m := by
    intro n m hn hm hlt
    obtain ⟨U, t, s, hU, hs, e⟩ := hn.2
    obtain ⟨s', e'⟩ := hm.1 U t
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = n + (k + 1 : ℕ) := ⟨(m - n - 1).toNat, by omega⟩
    have hp : algebraMap R K π ≠ 0 := by simpa using h0
    have hu : IsUnit (cstK A (M.j ⁻¹ᵁ U) (algebraMap R K π ^ n)) := (IsUnit.mk0 _ (zpow_ne_zero n hp)).map _
    rw [e, hk, zpow_add₀ hp, map_mul, _root_.mul_assoc, zpow_natCast, ← map_pow, ← j_cst, ← map_mul] at e'
    have := j_app_injective M U (hu.mul_left_cancel e')
    rw [this, pow_succ, map_mul] at hs
    exact not_isUnit_cst M U hU hπ (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hs))
  have := key hn hm
  have := key hm hn
  omega
end GlobalTheory.SS.Ord
