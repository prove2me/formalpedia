-- Prove2me | solution 1 for GlobalTheory.SS.Slope.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:55.923054+00:00
-- url     : https://prove2.me/submissions/947babab-1115-412d-a378-2253465f0764

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightedOrderSlopeComparison
import Theorems.Thm_GlobalTheory_SS_Slope_lt_iff

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Slope
open MvPowerSeries
variable {k : Type} [Field k]
namespace GlobalTheory.SS.Slope
theorem _root_.solution (f d : MvPowerSeries (Fin 2) k) (hf : ∀ t : Fin 2 →₀ ℕ, coeff t f ≠ 0 → 1 ≤ t 1)
    (s₀ : Fin 2 →₀ ℕ) (hs₀ : coeff s₀ d ≠ 0) (hs₀' : s₀ 1 = 0) (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (h : weightedOrder (![m, n] : Fin 2 → ℕ) f < weightedOrder (![m, n] : Fin 2 → ℕ) d) :
    ∃ p, n * (s₀ 0).factorial < m * p ∧
      ¬ weightedOrder (![(s₀ 0).factorial, p] : Fin 2 → ℕ) d <
        weightedOrder (![(s₀ 0).factorial, p] : Fin 2 → ℕ) f := by
  classical
  obtain ⟨t, ht, h⟩ := (lt_iff m n f d).1 h
  set N := (s₀ 0).factorial with hN
  have hNpos : 0 < N := Nat.factorial_pos _
  have ht1 := hf t ht
  have htle : t 1 ≤ s₀ 0 := by
    have := h s₀ hs₀
    rw [hs₀'] at this
    by_contra hc
    push Not at hc
    nlinarith [Nat.zero_le (m * t 0), Nat.mul_le_mul hmn hc.le]
  have hex : ∀ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 → s 1 < t 1 →
      ∃ p, N * t 0 + p * t 1 = N * s 0 + p * s 1 := by
    intro s hs hlt
    have h1 := h s hs
    have h2 : t 0 ≤ s 0 := by
      by_contra hc
      push Not at hc
      nlinarith [Nat.mul_le_mul_left m hc.le, Nat.mul_le_mul_left n hlt.le]
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le h2
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt.le
    have : b ∣ N := Nat.dvd_factorial (by omega) (by omega)
    obtain ⟨c, hc⟩ := this
    refine ⟨c * a, ?_⟩
    rw [ha, hb, hc]
    ring
  have hP : ∃ p, ∃ s : Fin 2 →₀ ℕ, coeff s d ≠ 0 ∧ s 1 < t 1 ∧
      N * t 0 + p * t 1 = N * s 0 + p * s 1 := by
    obtain ⟨p, hp⟩ := hex s₀ hs₀ (by omega)
    exact ⟨p, s₀, hs₀, by omega, hp⟩
  obtain ⟨s₁, hs₁, hlt₁, heq₁⟩ := Nat.find_spec hP
  set p := Nat.find hP with hp
  have hbig : n * N < m * p := by
    have h1 := h s₁ hs₁
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt₁.le
    rw [hb] at h1 heq₁
    have h2 : n * N * b < m * p * b := by nlinarith
    exact lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
  refine ⟨p, hbig, ?_⟩
  rw [lt_iff]
  rintro ⟨s, hs, hs'⟩
  have h3 := hs' t ht
  by_cases hlt : s 1 < t 1
  · obtain ⟨q, hq⟩ := hex s hs hlt
    have hpq : p ≤ q := Nat.find_min' hP ⟨s, hs, hlt, hq⟩
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt.le
    rw [hb] at h3 hq
    nlinarith [Nat.mul_le_mul_right b hpq]
  · push Not at hlt
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hlt
    have h1 := h s hs
    rw [hb] at h3 h1
    have h4 : N * s 0 + p * b < N * t 0 := by nlinarith
    have h5 : m * t 0 < m * s 0 + n * b := by nlinarith
    have h6 := Nat.mul_lt_mul_of_pos_left h4 (k := m) hm
    have h7 := Nat.mul_lt_mul_of_pos_left h5 (k := N) hNpos
    nlinarith [Nat.mul_le_mul_right b hbig.le]
end GlobalTheory.SS.Slope
