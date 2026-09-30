-- Prove2me | solution 1 for InfoSharing.Diseconomy.retailer_best_response
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:13:34.916386+00:00
-- url     : https://prove2.me/submissions/58d1ce82-1e70-45e7-b79e-6093353782fd

import Definitions.Def_InfoSharing_Shared_IsPricingEq
import Mathlib.Tactic
open InfoSharing.Shared
private theorem retailer_gap (a φ m : ℝ) (w p : Fin 2→ℝ) :
    retailerInterim a φ w m (fun i=>(a+m+w i)/2)-retailerInterim a φ w m p =
      (p 0-(a+m+w 0)/2)^2+(p 1-(a+m+w 1)/2)^2+
        φ*((p 0-(a+m+w 0)/2)-(p 1-(a+m+w 1)/2))^2 := by
  simp only [retailerInterim,Fin.sum_univ_two,other]
  norm_num
  ring

private theorem retailer_br (a φ β : ℝ) (hφ : 0<φ)
    (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) :
    IsRetailerBR a φ β ρ ↔ ∀ w y i,ρ w y i=(a+β*y+w i)/2 := by
  constructor
  · intro h w y i
    have hh := h w y (fun i=>(a+β*y+w i)/2)
    have hg := retailer_gap a φ (β*y) w (ρ w y)
    have hsq := mul_nonneg hφ.le (sq_nonneg ((ρ w y 0-(a+β*y+w 0)/2)-(ρ w y 1-(a+β*y+w 1)/2)))
    have h0 := sq_nonneg (ρ w y 0-(a+β*y+w 0)/2)
    have h1 := sq_nonneg (ρ w y 1-(a+β*y+w 1)/2)
    fin_cases i
    · change ρ w y 0=(a+β*y+w 0)/2
      nlinarith
    · change ρ w y 1=(a+β*y+w 1)/2
      nlinarith
  · intro h w y p
    have hρ : ρ w y=(fun i=>(a+β*y+w i)/2) := funext (h w y)
    rw [hρ]
    have hg := retailer_gap a φ (β*y) w p
    have hsq := mul_nonneg hφ.le (sq_nonneg ((p 0-(a+β*y+w 0)/2)-(p 1-(a+β*y+w 1)/2)))
    nlinarith [sq_nonneg (p 0-(a+β*y+w 0)/2),sq_nonneg (p 1-(a+β*y+w 1)/2)]

theorem solution {Ω : Type*} (a φ β : ℝ) (hφ : 0 < φ)
    (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) :
    (IsRetailerBR a φ β ρ ↔ ∀ (w : Fin 2 → ℝ) (y : ℝ) (i : Fin 2), ρ w y i = (a + β * y + w i) / 2) ∧
    ∀ (θ Y : Ω → ℝ) (f : Fin 2 → ℝ → ℝ) (i : Fin 2) (ω : Ω), IsRetailerBR a φ β ρ →
      demand a φ θ Y ρ f i ω =
        (a + β * Y ω - (1 + φ) * f i (Y ω) + φ * f (other i) (Y ω)) / 2 + (θ ω - β * Y ω) := by
  refine ⟨retailer_br a φ β hφ ρ,?_⟩
  intro θ Y f i ω h
  have hρ := (retailer_br a φ β hφ ρ).mp h
  unfold demand
  rw [hρ,hρ]
  ring
