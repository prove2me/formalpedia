-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermDecay.integrable_qZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:41:44.94057+00:00
-- url     : https://prove2.me/submissions/fce41997-1ada-4bc6-a40a-4ce2b09ae640

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableHeckeTermDecayIntegrand
import Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_continuous_qZ
import Theorems.Thm_GlobalTheory_HeckeTwo_TermDecay_norm_qZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
namespace GlobalTheory.HeckeTwo.TermDecay
theorem _root_.solution : ∀ σ ∈ halfPlane, ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∀ y : ℝ, y ≠ 0 →
    MeasureTheory.Integrable (qZ σ a b m y) := by
  intro σ hσ a b m hab y hy
  have hσ' : -1 / 2 < σ.re := hσ
  set e : ℝ := (a : ℝ) / 2 + b + σ.re with he
  have hab' : (2 : ℝ) ≤ a + 2 * b := by exact_mod_cast hab
  have he1 : 1 / 2 < e := by rw [he]; linarith
  set κ := min 1 (y ^ 2) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  refine (((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (r := 2 * e) (by simp; linarith)).const_mul
    (κ ^ (-e) * |y| ^ m))).mono' (continuous_qZ σ a b m hy).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t => ?_)
  rw [norm_qZ σ a b m hy t]
  have hQk : κ * (1 + ‖t‖ ^ 2) ≤ t ^ 2 + y ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    have h1 : κ ≤ 1 := min_le_left _ _
    have h2 : κ ≤ y ^ 2 := min_le_right _ _
    nlinarith [sq_nonneg t]
  have hA : (t ^ 2 + y ^ 2) ^ (-e) ≤ κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2) := by
    rw [show -(2 * e) / 2 = -e by ring, ← Real.mul_rpow hκ0.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hQk (by linarith)
  calc (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m ≤ (κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2)) * |y| ^ m :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring
end GlobalTheory.HeckeTwo.TermDecay
