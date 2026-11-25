-- Prove2me | solution 1 for GlobalTheory.RootEx.ColumnSupport.colE_inv_mul_affPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:49.773527+00:00
-- url     : https://prove2.me/submissions/1d91a2e1-85bc-4281-8b12-2877035b615d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ColEInvMulAffPt

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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ColumnSupport
namespace GlobalTheory.RootEx.ColumnSupport
theorem _root_.solution {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n]
    {c p : ℕ} (hp : p < c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (p + 1) rs} → k) (r : n) :
    (((colE c (p + 1) β)⁻¹).val * affPt (p + 1) x₀ e) (Sum.inl r) (Sum.inr ⟨p, by omega⟩) = -β r := by
  have hv : ((colE c (p + 1) β)⁻¹).val =
      fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p + 1 then β r else 0)) 0 1 := rfl
  have h1 : ∀ s : n, affPt (p + 1) x₀ e (Sum.inl s) (Sum.inr ⟨p, by omega⟩) = 0 := by
    intro s
    simp [affPt, basePt, Free]
  have h2 : affPt (p + 1) x₀ e (Sum.inr ⟨p, hp⟩) (Sum.inr ⟨p, by omega⟩) = 1 := by
    simp [affPt, basePt, Free]
  rw [hv, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [h1, mul_zero, Finset.sum_const_zero, zero_add, fromBlocks_apply₁₂]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : Fin c)]
  · simp [h2]
  · intro j _ hj
    have : j.val ≠ p := fun e => hj (Fin.ext e)
    simp [this]
  · simp
end GlobalTheory.RootEx.ColumnSupport
