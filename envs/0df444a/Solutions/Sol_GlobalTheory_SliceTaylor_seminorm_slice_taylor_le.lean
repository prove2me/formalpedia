-- Prove2me | solution 1 for GlobalTheory.SliceTaylor.seminorm_slice_taylor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:04:16.194875+00:00
-- url     : https://prove2.me/submissions/f5db8ecb-3a68-4d5f-a872-dc86e40a532a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
import Theorems.Thm_GlobalTheory_SliceTaylor_norm_padL_le
import Theorems.Thm_GlobalTheory_SliceTaylor_norm_inrL_le
import Theorems.Thm_GlobalTheory_SliceTaylor_norm_le_norm_elim_add
import Theorems.Thm_GlobalTheory_SliceTaylor_norm_iteratedFDeriv_pd_le
import Theorems.Thm_GlobalTheory_SliceTaylor_elim_add_padL
import Theorems.Thm_GlobalTheory_SchwartzTranslate_hasDerivAt_iteratedFDeriv_line
import Theorems.Thm_GlobalTheory_SchwartzTranslate_taylor_two
import Theorems.Thm_GlobalTheory_SliceOp_pd_apply
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SliceSchwartz.sliceR_apply



set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceTaylor
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.SliceTaylor
theorem _root_.solution (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (k n : ℕ) (x h : κ → V) :
    SchwartzMap.seminorm ℂ k n (sliceR f (x + h) - sliceR f x - sliceR (pd (padL (κ' := κ') h) f) x) ≤
      ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f := by
  set a : κ ⊕ κ' → V := padL (κ' := κ') h with ha
  set f1 := pd a f with hf1
  set f2 := pd a f1 with hf2
  set M := ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f with hM
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun y => ?_
  have hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have c1 : ContDiff ℝ ∞ f1 := f1.smooth'
  have e1 : (fun z => fderiv ℝ f z a) = ⇑f1 := by funext z; exact (pd_apply a f z).symm
  have e2 : (fun z => fderiv ℝ f1 z a) = ⇑f2 := by funext z; exact (pd_apply a f1 z).symm
  set G : (κ ⊕ κ' → V) → ℂ := fun w => f (w + a) - f w - f1 w with hG
  have cG : ContDiff ℝ ∞ G :=
    ((c0.comp (contDiff_id.add contDiff_const)).sub c0).sub c1
  set c : κ ⊕ κ' → V := Sum.elim x 0 with hc
  have efun : ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x)
      = (fun u => G (u + c)) ∘ ⇑(inrL (V := V) κ κ') := by
    funext y'
    have hy : (Sum.elim x y' : κ ⊕ κ' → V) = inrL κ κ' y' + c := by
      rw [add_comm]; exact congrFun (elim_eq_add x) y'
    simp only [SchwartzMap.sub_apply, sliceR_apply, Function.comp_apply, hG, ← hy,
      elim_add_padL, ha]
  have cGc : ContDiff ℝ ∞ (fun u => G (u + c)) := cG.comp (contDiff_id.add contDiff_const)
  have eit : iteratedFDeriv ℝ n ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x) y
      = (iteratedFDeriv ℝ n f (Sum.elim x y + a) - iteratedFDeriv ℝ n f (Sum.elim x y)
          - iteratedFDeriv ℝ n f1 (Sum.elim x y)).compContinuousLinearMap
          (fun _ => inrL (V := V) κ κ') := by
    have hy : inrL (V := V) κ κ' y + c = Sum.elim x y := by
      rw [add_comm]; exact (congrFun (elim_eq_add x) y).symm
    rw [efun, ContinuousLinearMap.iteratedFDeriv_comp_right _ cGc _ hnn, iteratedFDeriv_comp_add_right, hy]
    congr 1
    have ct : ContDiff ℝ ∞ (fun z => f (z + a)) := c0.comp (contDiff_id.add contDiff_const)
    change iteratedFDeriv ℝ n (((fun z => f (z + a)) - ⇑f) - ⇑f1) _ = _
    rw [iteratedFDeriv_sub_apply (f := (fun z => f (z + a)) - ⇑f) (g := ⇑f1) ((ct.sub c0).of_le hnn).contDiffAt (c1.of_le hnn).contDiffAt,
      iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt,
      iteratedFDeriv_comp_add_right]
  rw [eit]
  set z : κ ⊕ κ' → V := Sum.elim x y with hz
  have key := GlobalTheory.SchwartzTranslate.taylor_two (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f (z + s • a))
    (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f1 (z + s • a))
    (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f2 (z + s • a))
    (fun s => by
      have := GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f c0 z s
      rw [e1] at this
      exact this.const_smul (‖y‖ ^ k))
    (fun s => by
      have := GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f1 c1 z s
      rw [e2] at this
      exact this.const_smul (‖y‖ ^ k))
    M
    (fun s _ => by
      set w := z + s • a
      have hyw : ‖y‖ ≤ ‖w‖ := norm_le_norm_elim_add x h y s
      have b1 := norm_iteratedFDeriv_pd_le a f1 n w
      have b2 := norm_iteratedFDeriv_pd_le a f (n + 1) w
      have hah : ‖a‖ ≤ ‖h‖ := norm_padL_le h
      have hS := SchwartzMap.le_seminorm ℂ k (n + 2) f w
      have hb : ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖ := by
        calc ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) f1 w‖ := b1
          _ ≤ ‖a‖ * (‖a‖ * ‖iteratedFDeriv ℝ (n + 1 + 1) f w‖) := by gcongr
          _ ≤ ‖h‖ * (‖h‖ * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by gcongr
          _ = _ := by ring
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f2 w‖
          ≤ ‖w‖ ^ k * (‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by gcongr
        _ = ‖h‖ ^ 2 * (‖w‖ ^ k * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by ring
        _ ≤ M := by rw [hM]; gcongr) 1 (by simp)
  simp only [zero_smul, add_zero, one_smul, one_pow, mul_one] at key
  rw [← smul_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  calc ‖y‖ ^ k * ‖(iteratedFDeriv ℝ n f (z + a) - iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f1 z).compContinuousLinearMap
          (fun _ => inrL (V := V) κ κ')‖
      ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f (z + a) - iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f1 z‖ := by
        gcongr
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')
    _ ≤ M := key
end GlobalTheory.SliceTaylor
