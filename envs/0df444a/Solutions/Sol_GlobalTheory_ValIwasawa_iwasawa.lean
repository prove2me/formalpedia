-- Prove2me | solution 1 for GlobalTheory.ValIwasawa.iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:13.76182+00:00
-- url     : https://prove2.me/submissions/4d9897b2-59ef-4af5-a86a-92cfd50f2793

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOfValILeOne
import Theorems.Thm_GlobalTheory_ValIwasawa_iwasawa_matrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ValIwasawa
open Matrix
variable {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]
namespace GlobalTheory.ValIwasawa
theorem _root_.solution : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (N : ℕ) (g : GL (Fin N) K), ∃ (k : GL (Fin N) V) (b : GL (Fin N) K),
    b.1.BlockTriangular id ∧ g = GeneralLinearGroup.map (algebraMap V K) k * b := by
  intro V K _ _ _ _ _ _ N g
  obtain ⟨k, U, hk, hU, -, hg⟩ := iwasawa_matrix (V := V) g.1 (Matrix.GeneralLinearGroup.det_ne_zero g)
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det k).2 hk
  refine ⟨u, (GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u)⁻¹ * g, ?_, by simp⟩
  have : ((GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u)⁻¹ * g).1 = U := by
    have h1 : g.1 = (GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u).1 * U := hg
    rw [Units.val_mul, h1, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [this]
  exact hU
end GlobalTheory.ValIwasawa
