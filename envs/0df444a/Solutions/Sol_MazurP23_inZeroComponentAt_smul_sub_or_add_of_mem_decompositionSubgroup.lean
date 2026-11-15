-- Prove2me | solution 1 for MazurP23.inZeroComponentAt_smul_sub_or_add_of_mem_decompositionSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:10:26.218478+00:00
-- url     : https://prove2.me/submissions/15f78b31-2294-4dcc-8d98-3a7a7778e61e

import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_torsion_odd_of_not_inZeroComponentAt
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_slope_mem_of_shallow
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub_of_level_eq_of_branch_eq
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne
import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

namespace MazurP23

theorem _root_.solution (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσD : σ ∈ A.decompositionSubgroup ℚ)
    {n : ℕ} (hn : Odd n) (hn1 : 1 < n) (hnq : ¬ q ∣ n)
    (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (htor : n • x = 0) (hout : ¬ W.InZeroComponentAt A x) :
    W.InZeroComponentAt A (σ • x - x) ∨ W.InZeroComponentAt A (σ • x + x) := by
  classical

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction W hq hΔ hqΔ hqc₄ A hA

  rcases hP : x with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd (Or.inl hP) hout
  rw [hP] at hout htor
  have hX : A.valuation (x₁ - x₀) < 1 :=
    (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre
      W A hx₀ hy₀ hFy hFx hnode hbad h₁).mp hout

  obtain ⟨hns, hσsome⟩ : ∃ hns :
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular (σ x₁) (σ y₁),
      σ • (Point.some x₁ y₁ h₁ :
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
        = Point.some (σ x₁) (σ y₁) hns :=
    ⟨_, Point.map_some σ.toAlgHom h₁⟩

  have houtσ : ¬ W.InZeroComponentAt A (Point.some (σ x₁) (σ y₁) hns) := by
    intro hin
    refine hout ?_
    have h2 := WeierstrassCurve.inZeroComponentAt_smul W A
      (inv_mem hσD) (P := Point.some (σ x₁) (σ y₁) hns) hin
    rwa [← hσsome, inv_smul_smul] at h2
  have hXσ : A.valuation (σ x₁ - x₀) < 1 :=
    (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre
      W A hx₀ hy₀ hFy hFx hnode hbad hns).mp houtσ

  have hvmap : ∀ z : AlgebraicClosure ℚ, A.valuation (σ z) = A.valuation z := fun z =>
    ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A hσD z
  have hd0 : A.valuation (σ x₀ - x₀) < 1 := by
    have hsplit : σ x₀ - x₀ = (σ x₀ - σ x₁) + (σ x₁ - x₀) := by ring
    have h1 : A.valuation (σ x₀ - σ x₁) < 1 := by
      have : σ x₀ - σ x₁ = σ (x₀ - x₁) := (map_sub σ x₀ x₁).symm
      rw [this, hvmap, show x₀ - x₁ = -(x₁ - x₀) by ring, Valuation.map_neg]
      exact hX
    calc A.valuation (σ x₀ - x₀) ≤ max (A.valuation (σ x₀ - σ x₁)) (A.valuation (σ x₁ - x₀)) :=
          hsplit ▸ A.valuation.map_add _ _
      _ < 1 := max_lt h1 hXσ

  have hb₂ : ((W.b₂ : ℤ) : AlgebraicClosure ℚ)
      = ((W.a₁ : ℤ) : AlgebraicClosure ℚ) ^ 2 + 4 * ((W.a₂ : ℤ) : AlgebraicClosure ℚ) := by
    rw [show W.b₂ = W.a₁ ^ 2 + 4 * W.a₂ from rfl]; push_cast; ring
  have hb₄ : ((W.b₄ : ℤ) : AlgebraicClosure ℚ)
      = 2 * ((W.a₄ : ℤ) : AlgebraicClosure ℚ)
        + ((W.a₁ : ℤ) : AlgebraicClosure ℚ) * ((W.a₃ : ℤ) : AlgebraicClosure ℚ) := by
    rw [show W.b₄ = 2 * W.a₄ + W.a₁ * W.a₃ from rfl]; push_cast; ring
  have hcrit : 6 * x₀ ^ 2 + ((W.b₂ : ℤ) : AlgebraicClosure ℚ) * x₀
      + ((W.b₄ : ℤ) : AlgebraicClosure ℚ) = 0 := by
    rw [hb₂, hb₄]
    linear_combination ((W.a₁ : ℤ) : AlgebraicClosure ℚ) * hFy - 2 * hFx
  have hσcrit : 6 * (σ x₀) ^ 2 + ((W.b₂ : ℤ) : AlgebraicClosure ℚ) * (σ x₀)
      + ((W.b₄ : ℤ) : AlgebraicClosure ℚ) = 0 := by
    have h0 := congrArg σ hcrit
    simp only [map_add, map_mul, map_pow, map_ofNat, map_intCast, _root_.map_zero] at h0
    exact h0
  have hσx₀ : σ x₀ = x₀ := by
    have hfact : (x₀ - σ x₀) *
        (6 * (x₀ + σ x₀) + ((W.b₂ : ℤ) : AlgebraicClosure ℚ)) = 0 := by
      linear_combination hcrit - hσcrit
    rcases mul_eq_zero.mp hfact with h | h
    · exact (sub_eq_zero.mp h).symm
    · exfalso
      have heq : ((W.b₂ : ℤ) : AlgebraicClosure ℚ) + 12 * x₀ = 6 * (x₀ - σ x₀) := by
        linear_combination h
      have h6A : A.valuation (6 : AlgebraicClosure ℚ) ≤ 1 := by
        refine (ValuationSubring.valuation_le_one_iff A _).mpr ?_
        exact_mod_cast _root_.natCast_mem A 6
      have hlt : A.valuation (6 * (x₀ - σ x₀)) < 1 := by
        rw [Valuation.map_mul]
        calc A.valuation (6 : AlgebraicClosure ℚ) * A.valuation (x₀ - σ x₀)
            ≤ 1 * A.valuation (x₀ - σ x₀) := mul_le_mul_left h6A _
          _ = A.valuation (x₀ - σ x₀) := one_mul _
          _ < 1 := by
              rw [show x₀ - σ x₀ = -(σ x₀ - x₀) by ring, Valuation.map_neg]; exact hd0
      rw [heq] at hnode
      exact absurd hnode hlt.ne
  have hσy₀ : σ y₀ = y₀ := by
    have h0 := congrArg σ hFy
    simp only [map_add, map_mul, map_ofNat, map_intCast, _root_.map_zero] at h0
    rw [hσx₀] at h0
    have h2 : (2 : AlgebraicClosure ℚ) ≠ 0 := two_ne_zero
    exact mul_left_cancel₀ h2 (by linear_combination h0 - hFy)

  obtain ⟨hshΔ, -⟩ :=
    WeierstrassCurve.valuation_pow_eq_of_torsion_odd_of_not_inZeroComponentAt
      W hq hΔ hqΔ hqc₄ A hA hx₀ hy₀ hFy hFx hnode hbad hn hn1 hnq h₁ htor hX
  have hΔF := WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre
    W A hx₀ hy₀ hFy hFx hnode hbad
  rw [hΔF] at hshΔ

  obtain ⟨hΛA, -, -⟩ :=
    WeierstrassCurve.slope_mem_of_shallow W A hx₀ hy₀ hFy hFx h₁ hX hshΔ
  have hΛσA : σ ((y₁ - y₀) / (x₁ - x₀)) ∈ A :=
    ValuationSubring.mem_of_valuation_le_one A _
      (by rw [hvmap]; exact (ValuationSubring.valuation_le_one_iff A _).mpr hΛA)
  have hσlam : σ ((y₁ - y₀) / (x₁ - x₀)) = (σ y₁ - y₀) / (σ x₁ - x₀) := by
    rw [map_div₀, map_sub, map_sub, hσx₀, hσy₀]

  have hlev : A.valuation (σ x₁ - x₀) = A.valuation (x₁ - x₀) := by
    rw [show σ x₁ - x₀ = σ (x₁ - x₀) by rw [map_sub, hσx₀], hvmap]

  have hsubA : σ ((y₁ - y₀) / (x₁ - x₀)) - (y₁ - y₀) / (x₁ - x₀) ∈ A :=
    sub_mem hΛσA hΛA
  have hsuble : A.valuation ((σ y₁ - y₀) / (σ x₁ - x₀) - (y₁ - y₀) / (x₁ - x₀)) ≤ 1 := by
    rw [← hσlam]
    exact (ValuationSubring.valuation_le_one_iff A _).mpr hsubA
  rcases lt_or_eq_of_le hsuble with hbr | hbr
  ·
    left
    have hcloser :=
      WeierstrassCurve.inZeroComponentAt_sub_of_level_eq_of_branch_eq
        W A hx₀ hy₀ hFy hFx hnode hbad hns h₁ hXσ hX hlev
        (by rw [hlev]; exact hshΔ) hbr
    rw [hσsome]
    exact hcloser.1
  ·
    right
    have hcloser :=
      WeierstrassCurve.inZeroComponentAt_add_of_level_eq_of_branch_ne
        W A hx₀ hy₀ hFy hFx hnode hbad hns h₁ hXσ hX hlev
        (by rw [hlev]; exact hshΔ) hbr
    rw [hσsome]
    exact hcloser.1

end MazurP23
