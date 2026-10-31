-- Prove2me | solution 1 for MinBuying.mtp2_integrable_marginal
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:55:08.066958+00:00
-- url     : https://prove2.me/submissions/fde77b01-9415-4b7e-a2e9-7ba7e182af33

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory Set MinBuying
open scoped BigOperators
noncomputable section

namespace MinBuyingIntegrableMarginalProof

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

private lemma four_functions_integral {α : Type*} [LinearOrder α] [MeasurableSpace α]
    (μ : Measure α) (a b c d : α → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (hc : ∀ x, 0 ≤ c x) (hd : ∀ x, 0 ≤ d x)
    (h : ∀ x y, a x*b y ≤ c (min x y)*d (max x y))
    (ia : Integrable a μ) (ib : Integrable b μ) (ic : Integrable c μ) (id : Integrable d μ) :
    (∫ x, a x ∂μ)*(∫ x, b x ∂μ) ≤ (∫ x, c x ∂μ)*(∫ x, d x ∂μ) := by
  have hinner : ∀ x, a x*(∫ y,b y ∂μ)+(∫ y,a y ∂μ)*b x ≤
      c x*(∫ y,d y ∂μ)+(∫ y,c y ∂μ)*d x := by
    intro x
    have hh := integral_mono ((ib.const_mul (a x)).add (ia.mul_const (b x)))
      ((id.const_mul (c x)).add (ic.mul_const (d x)))
      (fun y => cross_pointwise a b c d ha hb hc hd h x y)
    simpa only [Pi.add_apply,integral_add (ib.const_mul _) (ia.mul_const _),
      integral_add (id.const_mul _) (ic.mul_const _),integral_const_mul,integral_mul_const] using hh
  have hh := integral_mono
    ((ia.mul_const (∫ y,b y ∂μ)).add (ib.const_mul (∫ y,a y ∂μ)))
    ((ic.mul_const (∫ y,d y ∂μ)).add (id.const_mul (∫ y,c y ∂μ))) hinner
  simp only [Pi.add_apply,integral_add (ia.mul_const _) (ib.const_mul _),
    integral_add (ic.mul_const _) (id.const_mul _),integral_const_mul,integral_mul_const] at hh
  linarith

end MinBuyingIntegrableMarginalProof

theorem solution (n : ℕ) (f : Valuations (n+1) → ℝ)
    (hf : ∀ v, 0 ≤ f v) (hmtp : MTP2 f) (μ : Measure ℝ)
    (hi : ∀ v : Valuations n, Integrable (fun t : ℝ => f (Fin.cons t v)) μ) :
    MTP2 (fun v : Valuations n => ∫ t : ℝ, f (Fin.cons t v) ∂μ) := by
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
  have hh := MinBuyingIntegrableMarginalProof.four_functions_integral μ
    (fun t => f (Fin.cons t v)) (fun t => f (Fin.cons t w))
    (fun t => f (Fin.cons t u)) (fun t => f (Fin.cons t z))
    (fun t => hf _) (fun t => hf _) (fun t => hf _) (fun t => hf _) hff
    (hi v) (hi w) (hi u) (hi z)
  simpa only [mul_comm] using hh
