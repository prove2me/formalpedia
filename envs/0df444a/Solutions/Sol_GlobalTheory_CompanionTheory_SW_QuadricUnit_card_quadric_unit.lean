-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricUnit.card_quadric_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:47:29.849824+00:00
-- url     : https://prove2.me/submissions/24970490-64be-494e-9a7d-3a7c0a52a77a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardQuadricUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricUnit_gauss_scale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_count_mul_card
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_norm_gauss


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricUnit
open GlobalTheory.CompanionTheory.SW.QuadricCount
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.QuadricUnit
theorem _root_.solution (hchar : ringChar k ≠ 2) (M : ℕ) (hM : Fintype.card ι = 2 * M)
    (hM1 : 1 ≤ M) (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) {s : k} (hs : s ≠ 0) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ (M - 1) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 :=
    AddChar.exists_apply_ne_zero.mpr one_ne_zero
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℕ := Nat.card {x : ι → k // quadForm B x = s} with hNdef
  have hcount := count_mul_card ψ hψ1 B s
  rw [← hNdef, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at hcount
  have hzero : ψ (-((0 : k) * s)) * ∑ x, ψ ((0 : k) * quadForm B x) =
      (Fintype.card k : ℂ) ^ (2 * M) := by
    simp [hM]
  rw [hzero] at hcount
  set G : ℂ := ∑ x, ψ (quadForm B x) with hG
  have hGn : ‖G‖ = (Fintype.card k : ℝ) ^ M := by
    have := norm_gauss ψ hψ1 h2 hB hdet hM (t := 1) one_ne_zero
    simpa [hG] using this
  have hrest : ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) = -G := by
    have e1 : ∀ t ∈ Finset.univ.erase (0 : k),
        ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) = ψ (t * (-s)) * G := by
      intro t ht
      rw [gauss_scale hchar ψ hψ1 hB hdet hM (Finset.ne_of_mem_erase ht), mul_neg]
    rw [Finset.sum_congr rfl e1, ← Finset.sum_mul]
    have e2 : ∑ t : k, ψ (t * (-s)) = 0 := by
      rw [AddChar.sum_mulShift (-s) (AddChar.IsPrimitive.of_ne_one hψ1)]
      simp [hs]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at e2
    have e3 : ∑ t ∈ Finset.univ.erase (0 : k), ψ (t * (-s)) = -1 := by
      simp only [zero_mul, AddChar.map_zero_eq_one] at e2
      linear_combination e2
    rw [e3]
    ring
  rw [hrest] at hcount
  have hreal : ((((N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) : ℝ)) : ℂ) = -G := by
    push_cast
    rw [hcount]
    ring
  have habs : |(N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M)| =
      (Fintype.card k : ℝ) ^ M := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal, norm_neg, hGn]
  have hpow : (Fintype.card k : ℝ) ^ (2 * M) =
      (Fintype.card k : ℝ) ^ (2 * M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) =
      ((N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)) * (Fintype.card k : ℝ) := by
    rw [hpow]
    ring
  have hpM : (Fintype.card k : ℝ) ^ M = (Fintype.card k : ℝ) ^ (M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hfac, abs_mul, abs_of_pos hq, hpM] at habs
  exact (mul_right_cancel₀ hq.ne' habs).le
end GlobalTheory.CompanionTheory.SW.QuadricUnit
