-- Prove2me | solution 1 for MinBuying.mtp2_summable_marginal
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:55:09.590416+00:00
-- url     : https://prove2.me/submissions/4a44d5b8-56ef-42ab-a22a-89cc114e4c51

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory Set MinBuying
open scoped BigOperators
noncomputable section

namespace MinBuyingSummableMarginalProof

private lemma cross_bound {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (h₀₀ : a₀*b₀ ≤ c₀*d₀) (h₁₀ : a₁*b₀ ≤ c₀*d₁)
    (h₀₁ : a₀*b₁ ≤ c₀*d₁) (h₁₁ : a₁*b₁ ≤ c₁*d₁) :
    a₀*b₁+a₁*b₀ ≤ c₀*d₁+c₁*d₀ := by
  by_cases hcd : c₀*d₁ = 0
  · nlinarith [mul_nonneg ha₀ hb₁,mul_nonneg ha₁ hb₀,mul_nonneg hc₁ hd₀]
  have hcdpos : 0 < c₀*d₁ := lt_of_le_of_ne (mul_nonneg hc₀ hd₁) (Ne.symm hcd)
  apply le_of_mul_le_mul_right _ hcdpos
  calc
    (a₀*b₁+a₁*b₀)*(c₀*d₁) = a₀*b₁*(c₀*d₁)+(c₀*d₁)*(a₁*b₀) := by ring
    _ ≤ a₀*b₁*(a₁*b₀)+(c₀*d₁)*(c₀*d₁) := mul_add_mul_le_mul_add_mul h₀₁ h₁₀
    _ = a₀*b₀*(a₁*b₁)+(c₀*d₁)*(c₀*d₁) := by ring
    _ ≤ c₀*d₀*(c₁*d₁)+(c₀*d₁)*(c₀*d₁) := by
      gcongr
    _ = (c₀*d₁+c₁*d₀)*(c₀*d₁) := by ring

private lemma cross_pointwise {α : Type*} [LinearOrder α] (a b c d : α → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (hc : ∀ x, 0 ≤ c x) (hd : ∀ x, 0 ≤ d x)
    (h : ∀ x y, a x*b y ≤ c (min x y)*d (max x y)) (x y : α) :
    a x*b y+a y*b x ≤ c x*d y+c y*d x := by
  rcases le_total x y with hxy | hyx
  · exact cross_bound (ha x) (ha y) (hb x) (hb y) (hc x) (hc y) (hd x) (hd y)
      (by simpa using h x x) (by simpa [min_eq_right hxy,max_eq_left hxy] using h y x)
      (by simpa [min_eq_left hxy,max_eq_right hxy] using h x y) (by simpa using h y y)
  · have hh := cross_bound (ha y) (ha x) (hb y) (hb x) (hc y) (hc x) (hd y) (hd x)
      (by simpa using h y y) (by simpa [min_eq_right hyx,max_eq_left hyx] using h x y)
      (by simpa [min_eq_left hyx,max_eq_right hyx] using h y x) (by simpa using h x x)
    simpa only [add_comm] using hh

private lemma four_functions_tsum {α : Type*} [LinearOrder α] (a b c d : α → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (hc : ∀ x, 0 ≤ c x) (hd : ∀ x, 0 ≤ d x)
    (h : ∀ x y, a x*b y ≤ c (min x y)*d (max x y))
    (sa : Summable a) (sb : Summable b) (sc : Summable c) (sd : Summable d) :
    (∑' x, a x)*(∑' x, b x) ≤ (∑' x, c x)*(∑' x, d x) := by
  have hinner : ∀ x, a x*(∑' y, b y)+(∑' y, a y)*b x ≤
      c x*(∑' y, d y)+(∑' y, c y)*d x := by
    intro x
    exact hasSum_le (fun y => cross_pointwise a b c d ha hb hc hd h x y)
      ((sb.hasSum.mul_left (a x)).add (sa.hasSum.mul_right (b x)))
      ((sd.hasSum.mul_left (c x)).add (sc.hasSum.mul_right (d x)))
  have hh := hasSum_le hinner
    ((sa.hasSum.mul_right (∑' y,b y)).add (sb.hasSum.mul_left (∑' y,a y)))
    ((sc.hasSum.mul_right (∑' y,d y)).add (sd.hasSum.mul_left (∑' y,c y)))
  linarith

end MinBuyingSummableMarginalProof

theorem solution (n : ℕ) (f : Valuations (n+1) → ℝ)
    (hf : ∀ v, 0 ≤ f v) (hmtp : MTP2 f)
    (hs : ∀ v : Valuations n, Summable (fun t : ℝ => f (Fin.cons t v))) :
    MTP2 (fun v : Valuations n => ∑' t : ℝ, f (Fin.cons t v)) := by
  intro v w
  let u : Valuations n := fun i => min (v i) (w i)
  let z : Valuations n := fun i => max (v i) (w i)
  have hff : ∀ s t : ℝ, f (Fin.cons s v)*f (Fin.cons t w) ≤
      f (Fin.cons (min s t) u)*f (Fin.cons (max s t) z) := by
    intro s t
    have hmin : (fun i : Fin (n+1) => (min ((Fin.cons s v : Valuations (n+1)) i) ((Fin.cons t w : Valuations (n+1)) i) : ℝ)) = (Fin.cons (min s t) u : Valuations (n+1)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [u]
    have hmax : (fun i : Fin (n+1) => (max ((Fin.cons s v : Valuations (n+1)) i) ((Fin.cons t w : Valuations (n+1)) i) : ℝ)) = (Fin.cons (max s t) z : Valuations (n+1)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [z]
    simpa only [hmin,hmax,mul_comm] using hmtp (Fin.cons s v) (Fin.cons t w)
  have hh := MinBuyingSummableMarginalProof.four_functions_tsum
    (fun t => f (Fin.cons t v)) (fun t => f (Fin.cons t w))
    (fun t => f (Fin.cons t u)) (fun t => f (Fin.cons t z))
    (fun t => hf _) (fun t => hf _) (fun t => hf _) (fun t => hf _) hff
    (hs v) (hs w) (hs u) (hs z)
  simpa only [mul_comm] using hh
