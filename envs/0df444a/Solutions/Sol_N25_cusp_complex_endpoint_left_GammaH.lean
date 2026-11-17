-- Prove2me | solution 1 for N25.cusp_complex_endpoint_left_GammaH
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:59.27007+00:00
-- url     : https://prove2.me/submissions/373f627a-4471-4923-a019-a8e610c69a8d

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_realizeOf_eq_div

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve UpperHalfPlane

open scoped MatrixGroups Topology

namespace N25

private theorem modular_value_nonzero_iff
    (Γ : Subgroup SL(2, ℤ)) {k : ℤ} (f : ModularForm Γ k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (τ : UpperHalfPlane) :
    f (γ • τ) ≠ 0 ↔ f τ ≠ 0 := by
  rw [SlashInvariantForm.slash_action_eqn_SL'' f hγ τ]
  have hd : (denom γ τ) ^ k ≠ 0 := zpow_ne_zero _ (denom_ne_zero γ τ)
  constructor
  · exact fun h => (mul_ne_zero_iff.mp h).2
  · exact fun h => mul_ne_zero hd h

private theorem realization_smul_of_mem
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (x : LaurentSeries ℂ) (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (τ : UpperHalfPlane) :
    realizeOf Γ x (γ • τ) = realizeOf Γ x τ := by
  classical
  by_cases ht : ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
      (p.2.2 : UpperHalfPlane → ℂ) τ ≠ 0 ∧
        x * ((qExpansion 1 (p.2.2 : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (p.2.1 : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
  · rcases ht with ⟨⟨k, g, h⟩, hτ, hx⟩
    have hγτ : h (γ • τ) ≠ 0 := (modular_value_nonzero_iff Γ h γ hγ τ).mpr hτ
    rw [realizeOf_eq_div Γ hT g h x hx (γ • τ) hγτ,
      realizeOf_eq_div Γ hT g h x hx τ hτ,
      SlashInvariantForm.slash_action_eqn_SL'' g hγ τ,
      SlashInvariantForm.slash_action_eqn_SL'' h hγ τ]
    field_simp [zpow_ne_zero _ (denom_ne_zero γ τ), hτ]
    <;> ring
  · have hnot : ¬ ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
        (p.2.2 : UpperHalfPlane → ℂ) (γ • τ) ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
      rintro ⟨⟨k, g, h⟩, hγτ, hx⟩
      exact ht ⟨⟨k, g, h⟩, (modular_value_nonzero_iff Γ h γ hγ τ).mp hγτ, hx⟩
    rw [realizeOf_of_not Γ x (γ • τ) hnot, realizeOf_of_not Γ x τ ht]

/-- Analytic cusp endpoints are unchanged by the actual left ΓH action. -/
theorem _root_.solution
    (endpoint : SL(2, ℤ) → AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField 25 N25.H25)))
    (hmem : ∀ (B : SL(2, ℤ))
      (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField 25 N25.H25)),
      x ∈ (endpoint B).toValuationSubring ↔ ∃ L : ℂ, Filter.Tendsto
        (fun τ : UpperHalfPlane => ModularCurve.realizeOf (CohCarrier.GammaH 25 N25.H25)
          (x : LaurentSeries ℂ) (B • τ)) UpperHalfPlane.atImInfty (nhds L))
    (γ B : SL(2, ℤ)) (hγ : γ ∈ CohCarrier.GammaH 25 N25.H25) :
    endpoint (γ * B) = endpoint B := by
  apply Place.ext
  apply SetLike.ext
  intro x
  rw [hmem, hmem]
  have he :
      (fun τ : UpperHalfPlane => realizeOf (CohCarrier.GammaH 25 N25.H25)
        (x : LaurentSeries ℂ) ((γ * B) • τ)) =
      (fun τ : UpperHalfPlane => realizeOf (CohCarrier.GammaH 25 N25.H25)
        (x : LaurentSeries ℂ) (B • τ)) := by
    funext τ
    rw [mul_smul]
    exact realization_smul_of_mem _ (translation_mem_GammaH 25 N25.H25) _ γ hγ (B • τ)
  rw [he]

end N25
