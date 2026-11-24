-- Prove2me | solution 1 for GlobalTheory.SW.SiegelSum.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:28:31.718197+00:00
-- url     : https://prove2.me/submissions/f2a5ba20-150c-4e2e-a36f-8610fdf4fe4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Theorems.Thm_GlobalTheory_SW_SiegelSum_exists_int_of_intM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelSum
namespace GlobalTheory.SW.SiegelSum
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (hR : 0 < R)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : ∃ M, ∀ x, ‖φ x‖ ≤ M := by
  classical
  let g : (κ → ι → Fin (R * R)) → ℝ := fun r => ‖φ (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R)‖
  refine ⟨∑ r, g r, fun x => ?_⟩
  by_cases hx : φ x = 0
  · rw [hx, norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨n, rfl⟩ := exists_int_of_intM hR (h.1 x hx)
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  let r : κ → ι → Fin (R * R) := fun k i => ⟨(n k i % (R * R)).toNat, by
    have := Int.emod_lt_of_pos (n k i) hRR
    have := Int.emod_nonneg (n k i) hRR.ne'
    zify; rw [Int.toNat_of_nonneg this]; assumption⟩
  have key := h.2 (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R)
    (Matrix.of fun k i => ((n k i / (R * R) : ℤ) : ℚ)) (fun k i => isIntegral_algebraMap (x := n k i / (R * R)))
  have he : (Matrix.of fun k i => (n k i : ℚ) / R) =
      (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R) +
        (R : ℚ) • (Matrix.of fun k i => ((n k i / (R * R) : ℤ) : ℚ)) := by
    ext k i
    have h1 : (((r k i : ℕ) : ℤ)) = n k i % (R * R) :=
      Int.toNat_of_nonneg (Int.emod_nonneg (n k i) hRR.ne')
    have h2 := Int.emod_add_mul_ediv (n k i) (R * R)
    rw [← h1] at h2
    have h3 : ((r k i : ℕ) : ℚ) + R * R * ((n k i / (R * R) : ℤ) : ℚ) = n k i := by
      exact_mod_cast h2
    have : (R : ℚ) ≠ 0 := by positivity
    simp only [of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← h3]
    field_simp
  rw [he, key]
  exact Finset.single_le_sum (f := g) (fun _ _ => norm_nonneg _) (Finset.mem_univ r)
end GlobalTheory.SW.SiegelSum
