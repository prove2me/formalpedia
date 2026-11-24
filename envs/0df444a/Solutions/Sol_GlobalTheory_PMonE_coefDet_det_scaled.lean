-- Prove2me | solution 1 for GlobalTheory.PMonE.coefDet_det_scaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:17:28.20642+00:00
-- url     : https://prove2.me/submissions/81cc62bc-95fd-45ae-94bb-7de31d6a8979

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
namespace GlobalTheory.PMonE
theorem _root_.solution {h : ℕ} (a lam y : Fin h → F) :
    (Matrix.of fun r j : Fin h => (a r * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ))).det =
      (∏ r, a r ^ p ^ (h - (r : ℕ))) * ((∏ j, y j ^ p ^ h) *
        (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det) := by
  rw [← Matrix.det_mul_row (fun j => y j ^ p ^ h), ← Matrix.det_mul_column (fun r => a r ^ p ^ (h - (r : ℕ)))]
  congr 1; ext r j
  simp only [Matrix.of_apply]
  have key : (y j ^ p ^ (r : ℕ)) ^ p ^ (h - (r : ℕ)) = y j ^ p ^ h := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' r.isLt.le]
  rw [mul_pow, mul_pow, key]
  ring
end GlobalTheory.PMonE
