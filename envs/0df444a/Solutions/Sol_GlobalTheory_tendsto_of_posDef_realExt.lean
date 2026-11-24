-- Prove2me | solution 1 for GlobalTheory.tendsto_of_posDef_realExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:53.208969+00:00
-- url     : https://prove2.me/submissions/e28c2697-b6e2-4147-9377-d76fa3494c4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_exists_pos_mul_sum_sq_le_of_posDef_realExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution [Module.Free ℤ X] [Module.Finite ℤ X]
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) : Tendsto Q cofinite atTop := by
  let b := Module.finBasis ℤ X
  obtain ⟨c, hc, h⟩ := exists_pos_mul_sum_sq_le_of_posDef_realExt b hQ
  refine tendsto_atTop.2 fun C => eventually_cofinite.2 ?_
  refine ((Set.finite_Icc (fun _ => -⌈C / c⌉) (fun _ => ⌈C / c⌉)).preimage
    b.equivFun.injective.injOn).subset fun x hx => ?_
  have hx' : Q x < C := not_le.1 hx
  have hi : ∀ i, |b.repr x i| ≤ ⌈C / c⌉ := fun i => by
    have h₁ : (b.repr x i : ℝ) ^ 2 ≤ ∑ i, (b.repr x i : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun i => (b.repr x i : ℝ) ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ i)
    have h₂ : (b.repr x i : ℝ) ^ 2 ≤ C / c := by
      rw [le_div_iff₀' hc]
      exact ((mul_le_mul_of_nonneg_left h₁ hc.le).trans (h x)).trans hx'.le
    have h₃ : (b.repr x i) ^ 2 ≤ ⌈C / c⌉ := by exact_mod_cast h₂.trans (Int.le_ceil _)
    refine le_trans ?_ h₃
    rw [← sq_abs]
    exact Int.le_self_sq _
  exact ⟨fun i => (abs_le.1 (hi i)).1, fun i => (abs_le.1 (hi i)).2⟩
end GlobalTheory
