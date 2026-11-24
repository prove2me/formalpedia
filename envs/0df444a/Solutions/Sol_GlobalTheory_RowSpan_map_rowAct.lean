-- Prove2me | solution 1 for GlobalTheory.RowSpan.map_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:12.784355+00:00
-- url     : https://prove2.me/submissions/12042596-15fd-4154-9975-ecc01a969dbb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_rowAct_X
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.RowSpan
theorem _root_.solution {K : Type} [Field K] (φ : k →+* K) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k)
    (P : MvPolynomial (Letter T r n) k) :
    map φ (rowAct g P) = rowAct (fun σ => φ.mapMatrix (g σ)) (map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp => simp [hp, rowAct_X]
end GlobalTheory.RowSpan
