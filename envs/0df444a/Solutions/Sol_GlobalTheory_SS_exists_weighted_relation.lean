-- Prove2me | solution 1 for GlobalTheory.SS.exists_weighted_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:41:14.043293+00:00
-- url     : https://prove2.me/submissions/5e2ddd66-2eb0-4c0d-8944-fed236bca6ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightedRelationOfMinimalSupport
import Theorems.Thm_GlobalTheory_SS_exists_minimal_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution :
    ∀ (F T X : Type) [Field F] [Group T] (c : T → X → F) (σ : T → F →+* F) (φ : T → F) (S : Finset X) (p q : X → F), (∀ t t' χ, c (t * t') χ = c t χ * c t' χ) → (∀ χ, c 1 χ = 1) → (∀ t t' χ, σ t (c t' χ) = c t' χ) → (∀ t t', σ t (φ t') = φ (t' * t)) → (∀ t, φ t * ∑ χ ∈ S, c t χ * p χ = ∑ χ ∈ S, c t χ * q χ) → ∑ χ ∈ S, p χ ≠ 0 → ∃ (χ₀ : X) (p' q' : X → F), ∑ χ ∈ S, p' χ ≠ 0 ∧ φ 1 * ∑ χ ∈ S, p' χ = ∑ χ ∈ S, q' χ ∧ ∀ t, ∀ χ ∈ S, σ t (p' χ) * c t χ₀ = c t χ * p' χ ∧ σ t (q' χ) * c t χ₀ = c t χ * q' χ := by
  intro F T X _ _ c σ φ S p q hmul hone hσc hσφ hrel hsum
  classical
  have hcinv : ∀ t χ, c t χ * c t⁻¹ χ = 1 := by
    intro t χ
    rw [← hmul, mul_inv_cancel, hone]
  obtain ⟨v', hMv', hLv', hmin⟩ := exists_minimal_support (S.disjSum S)
    (fun v : X ⊕ X → F => ∀ t, φ t * ∑ χ ∈ S, c t χ * v (Sum.inl χ) = ∑ χ ∈ S, c t χ * v (Sum.inr χ))
    (fun v => ∑ χ ∈ S, v (Sum.inl χ))
    (by
      intro v w a hv hw t
      have e1 : ∀ g h : X → F, ∑ χ ∈ S, c t χ * (g χ - a * h χ)
          = ∑ χ ∈ S, c t χ * g χ - a * ∑ χ ∈ S, c t χ * h χ := by
        intro g h
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun χ _ => by ring
      rw [e1 (fun χ => v (Sum.inl χ)) (fun χ => w (Sum.inl χ)),
        e1 (fun χ => v (Sum.inr χ)) (fun χ => w (Sum.inr χ))]
      linear_combination hv t - a * hw t)
    (by
      intro v w a
      rw [Finset.sum_sub_distrib, Finset.mul_sum])
    (Sum.elim p q) (fun t => hrel t) hsum
  obtain ⟨χ₀, hχ₀S, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hLv'
  set r := v' (Sum.inl χ₀) with hrdef
  have htw : ∀ t, ∀ t', φ t' * ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inl χ)))
      = ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inr χ))) := by
    intro t t'
    have h := congrArg (σ t) (hMv' (t' * t⁻¹))
    simp only [map_mul, map_sum, hσc, hσφ, inv_mul_cancel_right, hmul] at h
    have e : ∀ g : X → F, ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * g χ) = ∑ χ ∈ S, c t' χ * c t⁻¹ χ * g χ :=
      fun g => Finset.sum_congr rfl fun χ _ => (mul_assoc _ _ _).symm
    rw [e (fun χ => σ t (v' (Sum.inl χ))), e (fun χ => σ t (v' (Sum.inr χ)))]
    exact h
  have hfin : ∀ t, ∀ i ∈ S.disjSum S,
      σ t (r⁻¹ * v' i) * c t χ₀ = c t (Sum.elim id id i) * (r⁻¹ * v' i) := by
    intro t i hi
    have hsr : σ t r ≠ 0 := (map_ne_zero (σ t)).mpr hr
    have hz := hmin (fun j => c t⁻¹ (Sum.elim id id j) * σ t (v' j) - c t⁻¹ χ₀ * σ t r / r * v' j)
      (fun t' => by
        have e1 : ∀ g h : X → F, ∑ χ ∈ S, c t' χ * (g χ - c t⁻¹ χ₀ * σ t r / r * h χ)
            = ∑ χ ∈ S, c t' χ * g χ - c t⁻¹ χ₀ * σ t r / r * ∑ χ ∈ S, c t' χ * h χ := by
          intro g h
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun χ _ => by ring
        simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
        rw [e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inl χ))) (fun χ => v' (Sum.inl χ)),
          e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inr χ))) (fun χ => v' (Sum.inr χ))]
        linear_combination htw t t' - c t⁻¹ χ₀ * σ t r / r * hMv' t')
      (by
        intro j _ hj
        simp [hj])
      (Sum.inl χ₀) (Finset.inl_mem_disjSum.mpr hχ₀S) hr
      (by
        show c t⁻¹ χ₀ * σ t r - c t⁻¹ χ₀ * σ t r / r * r = 0
        rw [div_mul_cancel₀ _ hr, sub_self])
      i hi
    have e' : r * (c t⁻¹ (Sum.elim id id i) * σ t (v' i)) = c t⁻¹ χ₀ * σ t r * v' i := by
      have hz' : c t⁻¹ (Sum.elim id id i) * σ t (v' i) = c t⁻¹ χ₀ * σ t r / r * v' i :=
        sub_eq_zero.mp hz
      rw [hz']
      field_simp
    have hc := hcinv t (Sum.elim id id i)
    have hc0 := hcinv t χ₀
    have h1 : σ t r * (σ t r)⁻¹ = 1 := mul_inv_cancel₀ hsr
    have h2 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    rw [map_mul, map_inv₀]
    linear_combination ((σ t r)⁻¹ * r⁻¹ * c t (Sum.elim id id i) * c t χ₀) * e'
      - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀ * c t (Sum.elim id id i) * c t⁻¹ (Sum.elim id id i)) * h2
      - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀) * hc
      + (r⁻¹ * c t (Sum.elim id id i) * v' i * c t χ₀ * c t⁻¹ χ₀) * h1
      + (r⁻¹ * c t (Sum.elim id id i) * v' i) * hc0
  refine ⟨χ₀, fun χ => r⁻¹ * v' (Sum.inl χ), fun χ => r⁻¹ * v' (Sum.inr χ), ?_, ?_, ?_⟩
  · rw [← Finset.mul_sum]
    exact mul_ne_zero (inv_ne_zero hr) hLv'
  · have h1 := hMv' 1
    simp only [hone, _root_.one_mul] at h1
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← h1]
    ring
  · intro t χ hχ
    exact ⟨by simpa only [Sum.elim_inl, id_eq] using hfin t (Sum.inl χ) (Finset.inl_mem_disjSum.mpr hχ),
      by simpa only [Sum.elim_inr, id_eq] using hfin t (Sum.inr χ) (Finset.inr_mem_disjSum.mpr hχ)⟩
end GlobalTheory.SS
