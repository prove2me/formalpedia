-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.conj_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:39.4458+00:00
-- url     : https://prove2.me/submissions/6065bb70-ad17-4016-aadc-1c942b19a23b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongIndex
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ}
namespace GlobalTheory.CompanionTheory.CongIndex
theorem _root_.solution {ϖ : k} (h0 : ϖ ≠ 0) {a : Fin N → ℤ} {D : GL (Fin N) k}
    (hD : (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ (a i)))
    (g : GL (Fin N) k) (i j : Fin N) :
    ((D⁻¹ * g * D : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j
        - (1 : Matrix (Fin N) (Fin N) k) i j =
      ϖ ^ (a j - a i) * ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) := by
  have hDE : (D : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => ϖ ^ (-a i)) = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [zpow_neg]
    exact mul_inv_cancel₀ (zpow_ne_zero _ h0)
  have hinv : ((D⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal (fun i => ϖ ^ (-a i)) := by
    calc ((D⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        = ((D⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *
            ((D : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => ϖ ^ (-a i))) := by
          rw [hDE, mul_one]
      _ = _ := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [Units.val_mul, Units.val_mul, hinv, hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, sub_self, zpow_zero, one_mul]
    rw [zpow_neg]
    field_simp
  · simp only [Matrix.one_apply_ne hij, sub_zero]
    rw [zpow_sub₀ h0, zpow_neg]
    field_simp
end GlobalTheory.CompanionTheory.CongIndex
