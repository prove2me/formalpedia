-- Prove2me | solution 1 for GlobalTheory.RiemannRel.riemann_relations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:46.889655+00:00
-- url     : https://prove2.me/submissions/1e979d50-8930-42e2-a478-e14c316fde12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Theorems.Thm_GlobalTheory_RiemannRel_hermForm_col
import Theorems.Thm_GlobalTheory_RiemannRel_det_ne_zero
import Theorems.Thm_GlobalTheory_RiemannRel_symm_posDef
import Theorems.Thm_GlobalTheory_RiemannRel_differentiableOn_left_inverse
import Theorems.Thm_GlobalTheory_RiemannRel_of_cols_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.RiemannRel
variable {g : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {g : ℕ}
namespace GlobalTheory.RiemannRel
namespace _root_.GlobalTheory.RiemannRel
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ a b, D.EF (bas a) (bas b) = -_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) → (∀ P, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P → ∃ h τ : Matrix (Fin g) (Fin g) ℂ, (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) ∧ IsUnit h.det ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ h' τ' : Matrix (Fin g) (Fin g) ℂ, (∀ k, h' *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h' *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1) → h' = h ∧ τ' = τ) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolPeriods D ty B P → (∀ b ∈ B, (∀ k, h b *ᵥ P b (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ P b (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1)) → ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B ∧ DifferentiableOn ℂ (fun b => τ b i j) B := by
  intro E _ _ _ H D g ty bas hEF
  have hnorm : ∀ (Q : D.La →+ (Fin g → ℂ)) (h τ : Matrix (Fin g) (Fin g) ℂ),
      (∀ k, h *ᵥ Q (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
        h *ᵥ Q (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) →
      h * Matrix.of (fun i j => Q (bas (Pi.single (Sum.inl j) 1)) i) = 1 ∧
        τ = h * Matrix.of (fun i j => Q (bas (Pi.single (Sum.inr j) 1)) i) := by
    intro Q h τ hQ
    refine ⟨Matrix.ext_of_mulVec_single fun k => ?_, Matrix.ext_of_mulVec_single fun k => ?_⟩
    · rw [← Matrix.mulVec_mulVec,
        _root_.GlobalTheory.RiemannRel.of_cols_mulVec (fun j => Q (bas (Pi.single (Sum.inl j) 1))), (hQ k).1,
        Matrix.one_mulVec]
    · rw [← Matrix.mulVec_mulVec,
        _root_.GlobalTheory.RiemannRel.of_cols_mulVec (fun j => Q (bas (Pi.single (Sum.inr j) 1))), (hQ k).2]
  refine ⟨fun P hP => ?_, fun m B P h τ hP hh i j => ?_⟩
  · obtain ⟨-, -, -, -, G, hG, hpos, hIm⟩ := hP
    set A := Matrix.of (fun i j => P (bas (Pi.single (Sum.inl j) 1)) i) with hAdef
    set C := Matrix.of (fun i j => P (bas (Pi.single (Sum.inr j) 1)) i) with hCdef
    have hAcol : ∀ k, A *ᵥ Pi.single k 1 = P (bas (Pi.single (Sum.inl k) 1)) :=
      fun k => _root_.GlobalTheory.RiemannRel.of_cols_mulVec (fun j => P (bas (Pi.single (Sum.inl j) 1))) k
    have hCcol : ∀ k, C *ᵥ Pi.single k 1 = P (bas (Pi.single (Sum.inr k) 1)) :=
      fun k => _root_.GlobalTheory.RiemannRel.of_cols_mulVec (fun j => P (bas (Pi.single (Sum.inr j) 1))) k
    have hM : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0 := by
      intro j k
      rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAcol, hAcol, hIm, hEF]
      simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd, Pi.single_apply]
    have hN : ∀ j k,
        ((Aᵀ * G * C.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k := by
      intro j k
      rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hAcol, hCcol, hIm, hEF]
      simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd, Pi.single_apply, Matrix.one_apply, @eq_comm _ k j]
    have hK : ∀ j k, ((Cᵀ * G * C.map (starRingEnd ℂ)) j k).im = 0 := by
      intro j k
      rw [← _root_.GlobalTheory.RiemannRel.hermForm_col, hCcol, hCcol, hIm, hEF]
      simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd, Pi.single_apply]
    have hdet : A.det ≠ 0 := _root_.GlobalTheory.RiemannRel.det_ne_zero G A C hpos hM hN
    have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
    have hAC : A * (A⁻¹ * C) = C := Matrix.mul_nonsing_inv_cancel_left A C hu
    have hsp := _root_.GlobalTheory.RiemannRel.symm_posDef G A (A⁻¹ * C) hG hdet hpos hM
      (by rw [hAC]; exact hN) (by rw [hAC]; exact hK)
    refine ⟨A⁻¹, A⁻¹ * C, fun k => ⟨?_, ?_⟩, Matrix.isUnit_nonsing_inv_det A hu, hsp.1, hsp.2, ?_⟩
    · rw [← hAcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
    · rw [← hCcol, Matrix.mulVec_mulVec]
    · intro h' τ' hh'
      obtain ⟨h1, h2⟩ := hnorm P h' τ' hh'
      have hinv : h' = A⁻¹ := (Matrix.inv_eq_left_inv h1).symm
      exact ⟨hinv, by rw [h2, hinv]⟩
  · have hent : ∀ (s : Fin g ⊕ Fin g) (i : Fin g),
        DifferentiableOn ℂ (fun b => P b (bas (Pi.single s 1)) i) B :=
      fun s i => differentiableOn_pi.mp (hP.2 _) i
    have hdh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B :=
      _root_.GlobalTheory.RiemannRel.differentiableOn_left_inverse
        (fun b => Matrix.of fun i j => P b (bas (Pi.single (Sum.inl j) 1)) i) h
        (fun i j => hent _ i) (fun b hb => (hnorm (P b) (h b) (τ b) (hh b hb)).1)
    refine ⟨hdh i j, DifferentiableOn.congr
      (f := fun b => ∑ l, h b i l * P b (bas (Pi.single (Sum.inr j) 1)) l)
      (DifferentiableOn.fun_sum fun l _ => (hdh i l).mul (hent _ l)) fun b hb => ?_⟩
    rw [(hnorm (P b) (h b) (τ b) (hh b hb)).2]
    simp [Matrix.mul_apply]
end _root_.GlobalTheory.RiemannRel
end GlobalTheory.RiemannRel
