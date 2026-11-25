-- Prove2me | solution 1 for GlobalTheory.CommonValuation.exists_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:06:06.815389+00:00
-- url     : https://prove2.me/submissions/3cbc02a5-69c9-4ac2-b807-53399936f714

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationIndexValuationCompat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CommonValuation
namespace GlobalTheory.CommonValuation
theorem _root_.solution {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    (P : HeightOneSpectrum R) (u : Valuation F (WithZero (Multiplicative ℤ)))
    (h1 : ∀ r : R, u (algebraMap R F r) ≤ 1) (h2 : ∀ r : R, u (algebraMap R F r) < 1 ↔ r ∈ P.asIdeal) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : F, u x = P.valuation F x ^ e := by
  have hu : ∀ r : R, r ∉ P.asIdeal → u (algebraMap R F r) = 1 := fun r hr =>
    le_antisymm (h1 r) (not_lt.1 fun h => hr ((h2 r).1 h))
  have hone : ∀ x : F, P.valuation F x = 1 → u x = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx.le
    have hn : n ∉ P.asIdeal := by
      rw [← P.valuation_eq_one_iff_notMem (K := F), ← h, map_mul, hx, one_mul]
      exact (P.valuation_eq_one_iff_notMem (K := F)).2 d.2
    have := congrArg u h
    rwa [map_mul, hu _ d.2, hu _ hn, mul_one] at this
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ' : P.valuation F (algebraMap R F π) = WithZero.exp (-1) := (P.valuation_of_algebraMap π).trans hπ
  have l1 : (WithZero.exp (-1) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπ0 : algebraMap R F π ≠ 0 := fun h => by
    rw [h, map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  have hlt : u (algebraMap R F π) < 1 := (h2 π).2 ((P.valuation_lt_one_iff_mem (K := F) π).1 (hπ' ▸ l1))
  have hu0 : u (algebraMap R F π) ≠ 0 := by simpa using hπ0
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (u (algebraMap R F π)) = -(e : ℤ) ∧ 0 < e := by
    rw [← WithZero.exp_log hu0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    exact ⟨(-WithZero.log (u (algebraMap R F π))).toNat, by omega, by omega⟩
  refine ⟨e, he.2, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he.2.ne']
  have h0 : P.valuation F x ≠ 0 := by simpa using hx
  have h3 := hone (x * algebraMap R F π ^ WithZero.log (P.valuation F x)) (by
    rw [map_mul, map_zpow₀, hπ', ← WithZero.exp_zsmul]
    nth_rewrite 1 [← WithZero.exp_log h0]
    rw [← WithZero.exp_add]; simp)
  rw [map_mul, map_zpow₀, ← WithZero.exp_log hu0, he.1, ← WithZero.exp_zsmul,
    mul_eq_one_iff_eq_inv₀ WithZero.exp_ne_zero, ← WithZero.exp_neg] at h3
  rw [h3]
  nth_rewrite 2 [← WithZero.exp_log h0]
  rw [← WithZero.exp_nsmul]
  congr 1
  simp [mul_comm]
end GlobalTheory.CommonValuation
