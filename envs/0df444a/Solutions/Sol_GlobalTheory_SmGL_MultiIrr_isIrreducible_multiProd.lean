-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:36:37.59459+00:00
-- url     : https://prove2.me/submissions/7fdffb48-04c6-4d0d-8ed2-6a0bff6d2b08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_iff_of_equiv
import Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__c2ad73a9489a
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_multiProd_succ_equiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_multiProd_zero
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_multiProd
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_parInd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n a' b' n' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] [Fintype n'] [DecidableEq n']
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {s : ℕ} {m : Fin (s + 1) → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {s : ℕ} :
    ∀ {m : Fin s → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {n : Type} [Fintype n] [DecidableEq n]
    (e : (Σ i, m i) ≃ n) {X : Fin s → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    {σ : ∀ i, Representation ℂ (GL (m i) k) (X i)}, (∀ i, IsSmooth (σ i)) → (∀ i, (σ i).IsIrreducible) →
    (∀ i, IsUnitarisable (σ i)) → (multiProd e σ).IsIrreducible := by
  induction s with
  | zero => exact fun e _ _ _ σ _ _ _ => isIrreducible_multiProd_zero e σ
  | succ s ih =>
    intro m _ _ n _ _ e X _ _ σ hs hi hu
    obtain ⟨E⟩ := multiProd_succ_equiv e σ
    exact (isIrreducible_iff_of_equiv E).1 (isIrreducible_ind₂ H _ (hs 0) (hi 0) (hu 0) (isSmooth_parInd _ _)
      (ih _ (fun i => hs i.succ) (fun i => hi i.succ) fun i => hu i.succ)
      (UnitInd.isUnitarisable_multiProd _ fun i => hu i.succ))
end GlobalTheory.SmGL.MultiIrr
