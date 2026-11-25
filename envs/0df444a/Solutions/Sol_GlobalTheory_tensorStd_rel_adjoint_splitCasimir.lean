-- Prove2me | solution 1 for GlobalTheory.tensorStd_rel_adjoint_splitCasimir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:22:06.08219+00:00
-- url     : https://prove2.me/submissions/5d47d6d1-619e-49c4-9095-e784e3a52762

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorStdRelAdjointSplitCasimir

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → GlRel Et ∧ (∀ a b x y, inner ℂ (Et a b x) y = inner ℂ x (Et b a y)) ∧ Om.IsSymmetric ∧ ∀ a b, Om * Et a b = Et a b * Om := by
  intro V _ _ _ n E Et Om hE hadj hEt hOm
  have hv : ∀ a b c d v, E a b (E c d v) = E c d (E a b v) +
      ((if b = c then E a d v else 0) - if d = a then E c b v else 0) := by
    intro a b c d v
    have h := LinearMap.congr_fun (hE a b c d) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_iff_eq_add', h]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    refine LinearMap.ext fun y => PiLp.ext fun k => ?_
    have h1 : ((if b = c then Et a d else 0) - if d = a then Et c b else 0 :
        Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) y k =
        (if b = c then Et a d y k else 0) - if d = a then Et c b y k else 0 := by
      split_ifs <;> simp
    rw [h1]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, PiLp.sub_apply, hEt, map_add]
    rw [hv a b c d]
    split_ifs <;> (try simp only [map_zero]) <;> abel
  · intro a b x y
    simp only [PiLp.inner_apply, hEt, inner_add_left, inner_add_right, Finset.sum_add_distrib, hadj]
    congr 1
    have h1 : ∀ c, inner ℂ (if c = a then x b else 0) (y c) =
        if c = a then inner ℂ (x b) (y c) else 0 := by
      intro c; split_ifs <;> simp
    have h2 : ∀ c, inner ℂ (x c) (if c = b then y a else 0) =
        if c = b then inner ℂ (x c) (y a) else 0 := by
      intro c; split_ifs <;> simp
    simp [h1, h2]
  · intro x y
    simp only [PiLp.inner_apply, hOm, sum_inner, inner_sum, hadj]
    exact Finset.sum_comm
  · intro a b
    refine LinearMap.ext fun y => PiLp.ext fun k => ?_
    simp only [Module.End.mul_apply, hEt, hOm, map_add, map_sum, Finset.sum_add_distrib]
    have h1 : ∀ c, E c k (E a b (y c)) = _ := fun c => hv c k a b (y c)
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, apply_ite (E _ k), map_zero]
    by_cases h : k = a
    · simp [h, add_assoc]
    · simp [h]
end GlobalTheory
