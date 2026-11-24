-- Prove2me | solution 1 for GlobalTheory.AdLat.eq_zero_of_valued_le_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:49:13.494999+00:00
-- url     : https://prove2.me/submissions/47ed2392-348e-435d-99dc-03e18a637b0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
import Theorems.Thm_GlobalTheory_AdLat_exists_nat_valued_pow_le
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_exists_exp_neg_lt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.AdLat
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.AdLat
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F)
    (h : ∀ N : ℕ, 0 < N → Valued.v y ≤ Valued.v (N : v.adicCompletion F)) : y = 0 := by
  by_contra hy
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (γ := Valued.v y) (by simpa using hy)
  exact absurd ((h _ (pow_pos hp n)).trans (hpn n)) (not_le.2 hn)
end GlobalTheory.AdLat
