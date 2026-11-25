-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.vHalf_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:46:07.082479+00:00
-- url     : https://prove2.me/submissions/44c27254-a6cf-43e4-a84b-103690c01c30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
import Theorems.Thm_GlobalTheory_HCXi_VLev_gram_nonneg
import Theorems.Thm_GlobalTheory_HCXi_VLev_gram_zero
import Theorems.Thm_GlobalTheory_HCXi_VLev_gram_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.VLev
variable {k r' : ℕ} (M : Mat k (1 + r')) (h : Mat k r') (a : ℂ) (hM0 : M *ᵥ e0 k r' = a • e0 k r')
  (hM : ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, M *ᵥ liftVec k 1 r' w = liftVec k 1 r' (h *ᵥ w) + c • e0 k r')
include hM0
include hM
namespace GlobalTheory.HCXi.VLev
theorem _root_.solution (ha : a ≠ 0) : vHalf k (1 + r') M =
    Complex.normSq a ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) * vHalf k r' h := by
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.2 ha
  unfold vHalf
  rw [Fin.prod_univ_add, Fin.prod_univ_one, gram_zero M a hM0 _ rfl,
    gram_succ M h a hM0 hM (Fin.last _) (Fin.last _) (by simp; omega),
    Finset.prod_congr rfl (fun (b : Fin r') _ => by
      rw [gram_succ M h a hM0 hM _ b.castSucc (by simp; omega), mul_inv]),
    Finset.prod_mul_distrib, Real.mul_rpow hN.le (gram_nonneg _ _ _ _)]
  have : Complex.normSq a ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) =
      (Complex.normSq a)⁻¹ * (Complex.normSq a)⁻¹ ^ r' * Complex.normSq a ^ (-((k : ℝ) / 2)) := by
    rw [← pow_succ', inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hN.le, ← Real.rpow_add hN]
    congr 1; push_cast; ring
  rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring
end GlobalTheory.HCXi.VLev
