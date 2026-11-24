-- Prove2me | solution 1 for GlobalTheory.PMonE.coefDet_det_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:17:27.290006+00:00
-- url     : https://prove2.me/submissions/3e485bff-99e7-4e56-a054-92487de4c19e

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
theorem _root_.solution {h : ℕ} (lam : Fin h → F) :
    (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin h)) : ℤ) : F) *
        (Matrix.of fun r j : Fin h => (lam j ^ p) ^ p ^ (r : ℕ)).det := by
  rw [← Matrix.det_permute]
  congr 1; ext r j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply, Fin.val_rev, id]
  rw [← pow_mul, ← pow_succ']
  congr 2; have := r.isLt; omega
end GlobalTheory.PMonE
