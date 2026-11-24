-- Prove2me | solution 1 for GlobalTheory.HilbTensorExists.exists_pre_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:30:36.910049+00:00
-- url     : https://prove2.me/submissions/a42fd833-0cda-4bf7-b696-b2ac0f4434fd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCompleteDense
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.HilbTensorExists
namespace GlobalTheory.HilbTensorExists
theorem _root_.solution (n : ℕ) : ∀ (H : Fin n → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)],
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  induction n with
  | zero =>
    intro H _ _
    refine ⟨ℂ, inferInstance, inferInstance, fun _ => 1, fun x y => ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    simp
  | succ n ih =>
    intro H _ _
    obtain ⟨K, iK, iK', t, ht⟩ := ih (fun i => H i.castSucc)
    refine ⟨K ⊗[ℂ] H (Fin.last n), inferInstance, inferInstance,
      fun x => t (fun i => x i.castSucc) ⊗ₜ[ℂ] x (Fin.last n), fun x y => ?_⟩
    rw [TensorProduct.inner_tmul, ht, Fin.prod_univ_castSucc]
end GlobalTheory.HilbTensorExists
