-- Prove2me | solution 1 for MinBuying.mtp2_summable_association
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:06:55.5018+00:00
-- url     : https://prove2.me/submissions/c3187914-0756-4c71-8f92-5fe54cd2a6a6

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory Set MinBuying
open scoped BigOperators FinsetFamily
noncomputable section

namespace MinBuyingSummableAssociationProof

private lemma four_functions_summable {α : Type*} [DistribLattice α]
    (a b c d : α → ℝ)
    (ha : ∀ x,0 ≤ a x) (hb : ∀ x,0 ≤ b x) (hc : ∀ x,0 ≤ c x) (hd : ∀ x,0 ≤ d x)
    (h : ∀ x y,a x*b y ≤ c (x ⊓ y)*d (x ⊔ y))
    (sa : Summable a) (sb : Summable b) (sc : Summable c) (sd : Summable d) :
    (∑' x,a x)*(∑' x,b x) ≤ (∑' x,c x)*(∑' x,d x) := by
  classical
  apply le_of_tendsto' (Filter.Tendsto.mul sa.hasSum sb.hasSum)
  intro s
  have hfour := four_functions_theorem a b c d ha hb hc hd h s s
  have hsc : (∑ x ∈ s ⊼ s,c x) ≤ ∑' x,c x :=
    Summable.sum_le_tsum _ (fun x _ => hc x) sc
  have hsd : (∑ x ∈ s ⊻ s,d x) ≤ ∑' x,d x :=
    Summable.sum_le_tsum _ (fun x _ => hd x) sd
  exact hfour.trans (mul_le_mul hsc hsd (Finset.sum_nonneg (fun x _ => hd x)) (tsum_nonneg hc))

end MinBuyingSummableAssociationProof

theorem solution (n : ℕ) (w f g : Valuations n → ℝ)
    (hw : ∀ v,0 ≤ w v) (hmtp : MTP2 w)
    (hf0 : ∀ v,0 ≤ f v) (hg0 : ∀ v,0 ≤ g v) (hf : Monotone f) (hg : Monotone g)
    (sw : Summable w) (sf : Summable (fun v => w v*f v))
    (sg : Summable (fun v => w v*g v))
    (sfg : Summable (fun v => w v*(f v*g v))) :
    (∑' v,w v*f v)*(∑' v,w v*g v) ≤
      (∑' v,w v)*(∑' v,w v*(f v*g v)) := by
  apply MinBuyingSummableAssociationProof.four_functions_summable
    (fun v => w v*f v) (fun v => w v*g v) w (fun v => w v*(f v*g v))
    (fun v => mul_nonneg (hw v) (hf0 v)) (fun v => mul_nonneg (hw v) (hg0 v)) hw
    (fun v => mul_nonneg (hw v) (mul_nonneg (hf0 v) (hg0 v))) _ sf sg sw sfg
  intro v z
  have hm : w v*w z ≤ w (v ⊓ z)*w (v ⊔ z) := by
    simpa only [Pi.sup_def,Pi.inf_def,mul_comm] using hmtp v z
  have hfg : f v*g z ≤ f (v ⊔ z)*g (v ⊔ z) :=
    mul_le_mul (hf le_sup_left) (hg le_sup_right) (hg0 z) (hf0 _)
  have h := mul_le_mul hm hfg (mul_nonneg (hf0 v) (hg0 z)) (mul_nonneg (hw _) (hw _))
  calc
    w v*f v*(w z*g z) = (w v*w z)*(f v*g z) := by ring
    _ ≤ (w (v ⊓ z)*w (v ⊔ z))*(f (v ⊔ z)*g (v ⊔ z)) := h
    _ = _ := by ring
