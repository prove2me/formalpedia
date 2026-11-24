-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:23:03.386249+00:00
-- url     : https://prove2.me/submissions/ab93f810-1c0b-4117-b9a5-28e4e4031f89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsScaledNontrivialCharacter
import Theorems.Thm_GlobalTheory_CharDualMat_exists_ball_trivial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharConductor
namespace GlobalTheory.CompanionTheory.CharConductor
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k),
    valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧
      ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by
  intro k _ _ _ _ ψ hψ a c ha hc
  classical
  have hA : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨γ, hγ, hball⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hc0 : valuation k c ≠ 0 := by
    intro h0
    rw [map_eq_zero] at h0
    exact hc (by rw [h0, AddChar.map_zero_eq_one])
  obtain ⟨m, hm⟩ := exists_pow_lt₀ ha (Units.mk0 (γ / valuation k c) (div_ne_zero hγ hc0))
  rw [Units.val_mk0, lt_div_iff₀ (zero_lt_iff.mpr hc0)] at hm
  have hex : ∃ r : ℕ, ∀ μ ∈ 𝒪[k], ψ (μ * a ^ r * c) = 1 := by
    refine ⟨m, fun μ hμ => hball _ ?_⟩
    have hμ1 : valuation k μ ≤ 1 := (Valuation.mem_integer_iff _ _).mp hμ
    rw [map_mul, map_mul, map_pow]
    calc valuation k μ * valuation k a ^ m * valuation k c
        ≤ 1 * valuation k a ^ m * valuation k c := by gcongr
      _ = valuation k a ^ m * valuation k c := by rw [one_mul]
      _ < γ := hm
  have hfind := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hfind
    exact hc (by simpa using hfind 1 (one_mem _))
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmin := Nat.find_min hex (m := r) (by omega)
  push Not at hmin
  obtain ⟨μ, hμ, hne⟩ := hmin
  refine ⟨μ * a ^ r * c, hne, ⟨r, μ, hμ, rfl⟩, fun s hs => ?_⟩
  have h := hfind (s * μ) (mul_mem hs hμ)
  rw [hr] at h
  have e : s * a * (μ * a ^ r * c) = s * μ * a ^ (r + 1) * c := by ring
  rw [e]
  exact h
end GlobalTheory.CompanionTheory.CharConductor
