-- Prove2me | solution 1 for GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:41:04.051292+00:00
-- url     : https://prove2.me/submissions/28f49275-2b13-447d-b2cb-22836833cb8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfMemPowMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EqZeroOfMemMaximalPow
namespace GlobalTheory.EqZeroOfMemMaximalPow
theorem _root_.solution {R : Type} [CommRing R] [IsNoetherianRing R] (y : R)
    (h : ∀ i : MaximalSpectrum R × ℕ, y ∈ i.1.asIdeal ^ (i.2 + 1)) : y = 0 := by
  by_contra hy
  have hJ : LinearMap.ker (LinearMap.toSpanSingleton R R y) ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R y) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hy h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
  have hmem : y ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro i
    rcases i with _ | i
    · simp
    · have hi := h (⟨m, hm⟩, i)
      simpa [smul_eq_mul, Ideal.mul_top] using hi
  obtain ⟨⟨r, hr⟩, hry⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff m y).mp hmem
  have hJr : (1 - r) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R y) := by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, sub_smul, one_smul]
    exact sub_eq_zero.mpr hry.symm
  have h1 : (1 : R) ∈ m := by simpa using m.add_mem (hle hJr) hr
  exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
end GlobalTheory.EqZeroOfMemMaximalPow
