-- Prove2me | solution 1 for GlobalTheory.UnramOrder.exists_eq_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:18.935659+00:00
-- url     : https://prove2.me/submissions/367dfeda-1bc9-4326-87cb-c342a11398d9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramOrder
open IsLocalRing Polynomial
variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]
namespace GlobalTheory.UnramOrder
theorem _root_.solution (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) {ω : R} (hω : IsUnit (ω - c ω)) (x : R) :
    ∃ a b : R₀, x = algebraMap R₀ R a + algebraMap R₀ R b * ω := by
  obtain ⟨e, he⟩ := hω.exists_right_inv
  have he' : (c ω - ω) * c e = 1 := by simpa [hc] using congrArg c he
  have hce : c e = -e := by linear_combination (-e) * he' - (c e) * he
  obtain ⟨b, hb⟩ := hfix ((x - c x) * e) (by rw [map_mul, map_sub, hc, hce]; ring)
  obtain ⟨a, ha⟩ := hfix (x - algebraMap R₀ R b * ω) (by
    rw [map_sub, map_mul, hbase, hb]
    linear_combination (x - c x) * he)
  exact ⟨a, b, by rw [ha]; ring⟩
end GlobalTheory.UnramOrder
