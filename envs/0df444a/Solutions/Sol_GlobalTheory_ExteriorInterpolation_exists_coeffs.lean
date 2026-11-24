-- Prove2me | solution 1 for GlobalTheory.ExteriorInterpolation.exists_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:53.941081+00:00
-- url     : https://prove2.me/submissions/73e663e9-d4de-4bf6-8429-5fb37ff40712

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExteriorInterpolation
namespace GlobalTheory.ExteriorInterpolation
theorem _root_.solution (l : ℕ) (z : Fin l → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ a : ℕ → ℂ, (∀ w : ℂ, ∏ i, (w - z i) = ∑ k ∈ Finset.range (l + 1), a k * w ^ k) ∧
      ∑ k ∈ Finset.range (l + 1), ‖a k‖ ≤ 2 ^ l := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℂ, P = ∏ i, (Polynomial.X + Polynomial.C (-z i)) := ⟨_, rfl⟩
  refine ⟨fun k => P.coeff k, fun w => ?_, ?_⟩
  · have hdeg : P.natDegree < l + 1 := by
      have h1 := Polynomial.natDegree_prod_le (s := Finset.univ)
        (f := fun i => Polynomial.X + Polynomial.C (-z i))
      simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one] at h1
      rw [hP]
      omega
    rw [← Polynomial.eval_eq_sum_range' hdeg, hP, Polynomial.eval_prod]
    simp [sub_eq_add_neg]
  · calc ∑ k ∈ Finset.range (l + 1), ‖P.coeff k‖
          ≤ ∑ k ∈ Finset.range (l + 1), ((l.choose (l - k) : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ (Finset.univ : Finset (Fin l)).card := by
            simpa [Nat.lt_succ_iff] using hk
          rw [hP, Finset.prod_X_add_C_coeff _ _ hk']
          calc ‖∑ t ∈ (Finset.univ : Finset (Fin l)).powersetCard
                  ((Finset.univ : Finset (Fin l)).card - k), ∏ i ∈ t, -z i‖
              ≤ ∑ t ∈ (Finset.univ : Finset (Fin l)).powersetCard
                  ((Finset.univ : Finset (Fin l)).card - k), (1 : ℝ) := by
                apply norm_sum_le_of_le
                intro t _
                rw [norm_prod]
                exact Finset.prod_le_one (fun i _ => norm_nonneg _)
                  (fun i _ => by rw [norm_neg]; exact hz i)
            _ = ((l.choose (l - k) : ℕ) : ℝ) := by
                simp [Finset.card_powersetCard, Finset.card_univ]
      _ = ∑ k ∈ Finset.range (l + 1), ((l.choose k : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.choose_symm (by simpa [Nat.lt_succ_iff] using hk)]
      _ = 2 ^ l := by exact_mod_cast Nat.sum_range_choose l
end GlobalTheory.ExteriorInterpolation
