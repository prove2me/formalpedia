-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.multiProd_succ_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:07:00.197535+00:00
-- url     : https://prove2.me/submissions/b1ca702d-89da-4dfb-b3b1-d53cedc2ca7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_ind__parInd_equiv_f8687141444d
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_tensorCons_tmul
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
theorem _root_.solution (e : (Σ i, m i) ≃ n) {X : Fin (s + 1) → Type} [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (σ : ∀ i, Representation ℂ (GL (m i) k) (X i)) :
    Nonempty ((ind₂ ((headTail m).trans e)
      (extTensor (σ 0) (multiProd (Equiv.refl _) fun i : Fin s => σ i.succ))).Equiv (multiProd e σ)) := by
  refine ind₂_parInd_equiv e (σ 0) _ _ (tensorCons X) fun g x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v w =>
    induction w using PiTensorProduct.induction_on with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | smul_tprod c y =>
      simp only [TensorProduct.tmul_smul, map_smul, TensorProduct.map_tmul, piTensor_tprod, tensorCons_tmul]
      congr 2
      funext i
      induction i using Fin.cases <;> rfl
end GlobalTheory.SmGL.MultiIrr
