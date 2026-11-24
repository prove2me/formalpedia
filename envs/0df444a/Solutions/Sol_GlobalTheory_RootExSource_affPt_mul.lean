-- Prove2me | solution 1 for GlobalTheory.RootExSource.affPt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:40.66452+00:00
-- url     : https://prove2.me/submissions/13e3cab9-9a69-45a6-9749-a4b7987a8ecb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Theorems.Thm_GlobalTheory_RootExSource_affPt_nonfree
import Theorems.Thm_GlobalTheory_RootExSource_affPt_mul_nonfree

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
open GlobalTheory GlobalTheory.RootExSource
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}
open Classical
namespace GlobalTheory.RootExSource
theorem _root_.solution {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p x₀ e * g.val = affPt p x₀ ((linPart n p g).mulVec e +
      fun a => (basePt c x₀ * g.val - basePt c x₀) a.1.1 a.1.2) := by
  ext r s
  by_cases h : Free p (r, s)
  · have key : ((linPart n p g).mulVec e) ⟨(r, s), h⟩ =
        ∑ s', (if h : Free p (r, s') then e ⟨(r, s'), h⟩ else 0) * g.val s' s := by
      have h1 : ((linPart n p g).mulVec e) ⟨(r, s), h⟩ =
          ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)), (if b.1 = r then g.val b.2 s else 0) *
            (if h : Free p b then e ⟨b, h⟩ else 0) := by
        rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free p b)]
        rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ Free p b} => _)
          (fun b _ => by rw [dif_neg b.2, mul_zero]), add_zero]
        simp only [Matrix.mulVec, dotProduct, linPart, of_apply]
        refine Finset.sum_congr rfl fun b _ => by rw [dif_pos b.2]
      rw [h1, Fintype.sum_prod_type, Finset.sum_eq_single r]
      · simp [mul_comm]
      · intro r' _ hr
        simp [hr]
      · simp
    unfold affPt
    rw [Matrix.add_mul, Matrix.add_apply, Matrix.add_apply, of_apply, dif_pos h, Pi.add_apply, key]
    simp only [Matrix.mul_apply, Matrix.sub_apply, of_apply]
    ring
  · rw [affPt_mul_nonfree hg _ _ _ _ h, affPt_nonfree _ _ _ _ h]
end GlobalTheory.RootExSource
