-- Prove2me | solution 1 for GlobalTheory.AdLat.exists_limit_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:49:14.412684+00:00
-- url     : https://prove2.me/submissions/27411855-b9da-4dbb-b340-bb731a00b516

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
import Theorems.Thm_GlobalTheory_AdLat_valued_natCast_ne_zero
import Theorems.Thm_GlobalTheory_AdLat_exists_nat_valued_pow_le
import Theorems.Thm_GlobalTheory_Idele_exists_exp_neg_lt
import Theorems.Thm_GlobalTheory_Idele_exists_limit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.AdLat
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.AdLat
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : ℕ → v.adicCompletion F)
    (h : ∀ N m : ℕ, 0 < N → 0 < m →
      Valued.v (x (N * m) - x N) ≤ Valued.v (N : v.adicCompletion F)) :
    ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
      Valued.v (t - x N) ≤ Valued.v (N : v.adicCompletion F) := by
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_limit (K := F) v (fun n => x (p ^ n)) (fun m n hnm => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add]
    exact (h _ _ (pow_pos hp n) (pow_pos hp k)).trans (hpn n))
  refine ⟨t, fun N hN => ?_⟩
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (valued_natCast_ne_zero v hN)
  have h1 := (ht n).trans hn.le
  have h2 := ((h _ _ (pow_pos hp n) hN).trans (hpn n)).trans hn.le
  have h3 := h _ _ hN (pow_pos hp n)
  have e : t - x N = (t - x (p ^ n)) - (x (p ^ n * N) - x (p ^ n)) + (x (N * p ^ n) - x N) := by
    rw [mul_comm N]; ring
  rw [e]
  exact Valuation.map_add_le _ (Valuation.map_sub_le _ h1 h2) h3
end GlobalTheory.AdLat
