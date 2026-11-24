-- Prove2me | solution 1 for GlobalTheory.RowSpan.rowInv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:00.266168+00:00
-- url     : https://prove2.me/submissions/d0f7f31e-0d77-4cdc-b220-376dd7eb895e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_P2M_GlobalTheory_RowTriangular_eval__shift_2e105f77a3c7
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
theorem _root_.solution [Infinite k] {K : Type} [Field K] (φ : k →+* K) {P : MvPolynomial (Letter T r n) k}
    (hP : RowInv r n k P) : RowInv r n K (map φ P) := by
  classical
  intro σ i i' hi t
  have := GlobalTheory.RowTriangular.eval₂_shift ((C : K →+* MvPolynomial (Letter T r n) K).comp φ) hP σ i i' hi (C t) X
    (fun ℓ => rowShift r n K σ i i' t (X ℓ)) (fun b => by simp [rowShift]) (fun ℓ hℓ => by
      rw [rowShift, aeval_X, if_neg hℓ])
  have e : ∀ Q : MvPolynomial (Letter T r n) k, rowShift r n K σ i i' t (map φ Q) =
      eval₂Hom ((C : K →+* MvPolynomial (Letter T r n) K).comp φ) (fun ℓ => rowShift r n K σ i i' t (X ℓ)) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => simp [rowShift]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p s hp => simp only [map_mul, hp, map_X, eval₂Hom_X']
  rw [e, this, map_eq_eval₂Hom_C_comp]
end GlobalTheory.RowSpan
