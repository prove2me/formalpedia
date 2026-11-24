-- Prove2me | solution 1 for GlobalTheory.NormTower.exists_norm_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:14.329469+00:00
-- url     : https://prove2.me/submissions/0ae62572-bf40-46bc-8e5c-e8ef661eee3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompatibleNormTowerProfinite
import Theorems.Thm_GlobalTheory_NormTower_exists_eventually_dvd_sub
import Theorems.Thm_GlobalTheory_T_exists_hostNorm_mod_coprime_level_half


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.NormTower
namespace GlobalTheory.NormTower
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (ν : ℕ → ℤ), (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) → (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) → ∃ t : ℕ → 𝓞 E, (∀ n : ℕ, 0 < n → (n : 𝓞 E) ∣ t n * H.bar (t n) - (ν n : 𝓞 E)) ∧ (∀ n m : ℕ, 0 < n → 0 < m → (n : 𝓞 E) ∣ t (n * m) - t n) ∧ t l.M - 1 ∈ l.Mb := by
  intro E _ _ _ H l ν hcop hcomp
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hs : ∀ j : ℕ, ∃ t : 𝓞 E, ((j.factorial : ℕ) : 𝓞 E) ∣ t * H.bar t - (ν j.factorial : 𝓞 E) ∧
      (l.M ∣ j.factorial → t - 1 ∈ l.Mb) := fun j =>
    GlobalTheory.T.exists_hostNorm_mod_coprime_level_half E H l j.factorial (ν j.factorial) j.factorial_pos (hcop _ j.factorial_pos)
  choose s hs1 hs2 using hs
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : ∀ n : ℕ, 0 < n → ∀ᶠ j in (U : Filter ℕ), n ∣ j.factorial := by
    intro n hn
    have h : ∀ᶠ j : ℕ in Filter.cofinite, n ∣ j.factorial := by
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop n] with j hj
      exact Nat.dvd_factorial hn hj
    exact h.filter_mono Filter.hyperfilter_le_cofinite
  have ht : ∀ n : ℕ, ∃ t : 𝓞 E, 0 < n → ∀ᶠ j in (U : Filter ℕ), (n : 𝓞 E) ∣ s j - t := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨t, h⟩ := exists_eventually_dvd_sub U s n hn
      exact ⟨t, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose t ht using ht
  refine ⟨t, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨j, ⟨a, ha⟩, m, hm⟩ := ((ht n hn).and (hU n hn)).exists
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [hm, h, mul_zero]) j.factorial_ne_zero
      · exact h
    obtain ⟨b, hb⟩ := hs1 j
    obtain ⟨c, hc⟩ := hcomp n m hn hm0
    rw [hm] at hb
    have hc' : ((ν (n * m) : ℤ) : 𝓞 E) - (ν n : 𝓞 E) = (n : 𝓞 E) * (c : 𝓞 E) := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hc
    have hsj : s j = t n + n * a := by rw [← ha]; ring
    rw [hsj, map_add, map_mul, map_natCast] at hb
    push_cast at hb
    exact ⟨m * b + c - (a * H.bar (t n) + t n * H.bar a + n * a * H.bar a), by linear_combination hb + hc'⟩
  · intro n m hn hm
    obtain ⟨j, h1, h2⟩ := ((ht n hn).and (ht (n * m) (Nat.mul_pos hn hm))).exists
    have h3 : (n : 𝓞 E) ∣ s j - t (n * m) := dvd_trans ⟨(m : 𝓞 E), by push_cast; rfl⟩ h2
    have := dvd_sub h1 h3
    convert this using 1
    ring
  · obtain ⟨j, ⟨a, ha⟩, h2⟩ := ((ht l.M hM).and (hU l.M hM)).exists
    have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
      have : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
      rw [← l.prod] at this
      exact Ideal.mul_le_left this
    have h3 : (l.M : 𝓞 E) * a ∈ l.Mb := Ideal.mul_mem_right a _ hMb
    have h4 : t l.M - 1 = (s j - 1) - (l.M : 𝓞 E) * a := by rw [← ha]; ring
    rw [h4]
    exact Ideal.sub_mem _ (hs2 j h2) h3
end GlobalTheory.NormTower
