-- Prove2me | solution 1 for GlobalTheory.RootEx.TargetUnip.linPart_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:20.818583+00:00
-- url     : https://prove2.me/submissions/e74ee2c4-526c-45cb-9144-4e1253c6c506

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.TargetUnip
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
open Classical
namespace GlobalTheory.RootEx.TargetUnip
theorem _root_.solution (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (a : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    (linPart p h).mulVec e a =
      ∑ r', h a.1.1 r' * (if hf : Free p (r', a.1.2) then e ⟨(r', a.1.2), hf⟩ else 0) := by
  let F : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k := fun b =>
    (if a.1.2 = b.2 then h a.1.1 b.1 else 0) * (if hf : Free p b then e ⟨b, hf⟩ else 0)
  have h1 : (linPart p h).mulVec e a = ∑ b : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}, F b.1 := by
    simp only [Matrix.mulVec, dotProduct, linPart, Matrix.of_apply, F]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dif_pos b.2]
  have h2 : ∑ b : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}, F b.1 = ∑ b, F b := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun b => Free p b) (by simp) F]
    refine Finset.sum_filter_of_ne fun b _ hb => ?_
    by_contra hf
    exact hb (by simp [F, hf])
  rw [h1, h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [Finset.sum_eq_single a.1.2]
  · simp [F]
  · intro s _ hs
    simp [F, hs.symm]
  · simp
end GlobalTheory.RootEx.TargetUnip
