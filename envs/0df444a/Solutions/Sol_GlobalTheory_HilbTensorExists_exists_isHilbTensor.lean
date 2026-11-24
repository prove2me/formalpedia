-- Prove2me | solution 1 for GlobalTheory.HilbTensorExists.exists_isHilbTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:04.171833+00:00
-- url     : https://prove2.me/submissions/9a504895-2203-4aeb-9142-2b623a00ae3c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCompleteDense
import Theorems.Thm_GlobalTheory_HilbTensorExists_exists_pre
import Theorems.Thm_GlobalTheory_HilbTensorExists_exists_complete_dense
import Theorems.Thm_GlobalTheory_HilbTensorExists_exists_extension
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
theorem _root_.solution (I : AutInst) (H : NumberField.InfinitePlace I.F → Type)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (hσ : ∀ v (g : Formalism.REAL.UJ (I.ε v)) x y, ⟪σ v (uMat g) x, σ v (uMat g) y⟫_ℂ = ⟪x, y⟫_ℂ) :
    ∃ (Hs : Type) (_ : NormedAddCommGroup Hs) (_ : InnerProductSpace ℂ Hs) (_ : CompleteSpace Hs)
      (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs), I.IsHilbTensor σ σs tens := by
  obtain ⟨K, iK, iK', t, ht⟩ := exists_pre H
  obtain ⟨L, iL, iL', iL'', s, hs, hd⟩ := exists_complete_dense t
  have hext : ∀ g : I.Ginf, ∃ T : L →L[ℂ] L,
      ∀ x, T (s x) = s (fun v => σ v (uMat (g v)) (x v)) := by
    intro g
    refine exists_extension s hd (fun x v => σ v (uMat (g v)) (x v)) (fun x y => ?_)
    simp only [hs, ht]
    exact Finset.prod_congr rfl fun v _ => hσ v (g v) (x v) (y v)
  choose σs hσs using hext
  refine ⟨L, iL, iL', iL'', σs, s, ?_⟩
  unfold Formalism.MainNotions.S.AutInst.IsHilbTensor
  exact ⟨fun x y => by rw [hs, ht], hσs, hd⟩
end GlobalTheory.HilbTensorExists
