-- Prove2me | solution 1 for GlobalTheory.LeadingMinorInv.minor_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:14:54.284281+00:00
-- url     : https://prove2.me/submissions/0fc089f0-5d1c-491c-8702-f003c9f57563

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
import Theorems.Thm_GlobalTheory_LeadingMinorInv_minor_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.LeadingMinorInv
open Formalism.QuantumDeterminants
namespace GlobalTheory.LeadingMinorInv
theorem _root_.solution {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((Uᴴ * A).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have e : Uᴴ * A = (Aᴴ * U)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [e, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, minor_mul hl _ _ hU,
    ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, star_star]
end GlobalTheory.LeadingMinorInv
