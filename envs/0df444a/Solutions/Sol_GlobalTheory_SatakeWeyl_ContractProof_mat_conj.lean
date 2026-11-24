-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.ContractProof.mat_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:13.306833+00:00
-- url     : https://prove2.me/submissions/8d37c475-bdfe-4c9d-81d3-6e6292537d20

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDominantDiagonalConjugationContracts
import Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_mat_inv_diag
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
noncomputable section
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.ContractProof
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.SatakeWeyl.ContractProof
theorem _root_.solution {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (i l : Fin r) :
    mat (s * g * s⁻¹) i l = ϖ ^ (c i - c l) * mat g i l := by
  rw [mat_mul, mat_mul, mat_inv_diag h0 c s hs, hs, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg,
    zpow_add₀ h0]
  ring
end GlobalTheory.SatakeWeyl.ContractProof
