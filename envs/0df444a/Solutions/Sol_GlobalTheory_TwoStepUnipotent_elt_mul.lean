-- Prove2me | solution 1 for GlobalTheory.TwoStepUnipotent.elt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:07.995932+00:00
-- url     : https://prove2.me/submissions/245b533a-32bd-478c-a417-a2d757b68bbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_mul_aux

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.TwoStepUnipotent
variable {S : Type} [Ring S] (st : S →+ S) (e₁ e₃ h : S)
variable {st e₁ e₃ h}
namespace GlobalTheory.TwoStepUnipotent
theorem _root_.solution (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {b w b' w' : S} (hb : e₃ * b = 0 ∧ b * e₃ = b) (hb' : e₃ * b' = 0 ∧ b' * e₃ = b')
    (hw : w * e₃ = w) (hw' : e₁ * w' = w') :
    elt st h b w * elt st h b' w'
      = elt st h (b + b') (w + w' + h * (st b' * b - st b * b')) := by
  have he3 : st e₃ = e₁ := by rw [← hs, hi]
  have sb' : e₁ * st b' = st b' := by
    calc e₁ * st b' = st (b' * e₃) := by rw [hm, he3]
      _ = st b' := by rw [hb'.2]
  have sb : st b * e₁ = 0 := by
    calc st b * e₁ = st (e₃ * b) := by rw [hm, he3]
      _ = 0 := by rw [hb.1, map_zero]
  have hz : (w - h * (st b * b)) * e₃ = w - h * (st b * b) := by
    rw [sub_mul, hw, mul_assoc, mul_assoc, hb.2]
  have hz' : e₁ * (w' - h * (st b' * b')) = w' - h * (st b' * b') := by
    rw [mul_sub, hw', ← mul_assoc, ← hc e₁, mul_assoc, ← mul_assoc e₁, sb']
  have hprod := mul_aux (c := st b) (c' := st b') h31 hb.2 hz hb'.1 sb' hz' sb
  have e : ∀ x : S, x = h * x + h * x := fun x => by rw [← add_mul, hh, one_mul]
  simp only [elt]
  rw [hprod]
  conv_lhs => rw [e (st b * b')]
  simp only [map_add, add_mul, mul_add, mul_sub]
  abel
end GlobalTheory.TwoStepUnipotent
