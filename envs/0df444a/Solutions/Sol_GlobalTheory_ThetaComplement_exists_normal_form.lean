-- Prove2me | solution 1 for GlobalTheory.ThetaComplement.exists_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:48:22.997327+00:00
-- url     : https://prove2.me/submissions/4eff1514-b46a-4b26-a180-4c82c3df9509

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsComplementaryThetaOfLinearMap
import Theorems.Thm_GlobalTheory_ThetaComplement_dot_symm
import Theorems.Thm_GlobalTheory_ThetaComplement_im_form
import Theorems.Thm_GlobalTheory_ThetaComplement_exists_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaComplement
namespace GlobalTheory.ThetaComplement
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τ ∈ SiegelH (Fin g))
    (huniq : ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) :
    ∃ (H : Matrix (Fin g) (Fin g) ℂ) (s : (Fin g → ℂ) → ℤ) (Q : (Fin g → ℂ) → ℂ),
      H.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) ∧
      Differentiable ℂ Q ∧
      (∀ l ∈ periodLattice τ, ∀ m ∈ periodLattice τ, ∃ k : ℤ,
        (s (l + m) : ℂ) = s l + s m + ((l ⬝ᵥ H.mulVec (star m)).im : ℂ) + 2 * k) ∧
      ∀ (n n' : Fin g → ℤ) (l z : Fin g → ℂ), l = τ *ᵥ ofIntVec n + ofIntVec n' →
        2 * π * I * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)
          = -(π * I * s l + π * (z ⬝ᵥ H.mulVec (star l)) + π / 2 * (l ⬝ᵥ H.mulVec (star l))
            + Q (z + l) - Q z) := by
  classical
  obtain ⟨H, hH, hS, hpos, hst⟩ := exists_form τ hτ
  have hs : ∃ s : (Fin g → ℂ) → ℤ, ∀ n n' : Fin g → ℤ,
      s (τ *ᵥ ofIntVec n + ofIntVec n') = n ⬝ᵥ n' := by
    refine ⟨fun w => if h : ∃ p : (Fin g → ℤ) × (Fin g → ℤ),
      w = τ *ᵥ ofIntVec p.1 + ofIntVec p.2 then h.choose.1 ⬝ᵥ h.choose.2 else 0, fun n n' => ?_⟩
    have h : ∃ p : (Fin g → ℤ) × (Fin g → ℤ),
      τ *ᵥ ofIntVec n + ofIntVec n' = τ *ᵥ ofIntVec p.1 + ofIntVec p.2 := ⟨(n, n'), rfl⟩
    simp only [dif_pos h]
    have h1 := h.choose_spec
    generalize h.choose = p at h1
    obtain ⟨h2, h3⟩ := huniq (p.1 + -n) (p.2 + -n') (by
      rw [ofIntVec_add, ofIntVec_add, ofIntVec_neg, ofIntVec_neg, mulVec_add, mulVec_neg]
      linear_combination (exp := 1) -h1)
    rw [add_neg_eq_zero] at h2 h3
    rw [h2, h3]
  obtain ⟨s, hs⟩ := hs
  have hcast : ∀ n n' : Fin g → ℤ, ((n ⬝ᵥ n' : ℤ) : ℂ) = ofIntVec n ⬝ᵥ ofIntVec n' := by
    intro n n'
    simp [dotProduct, ofIntVec]
  refine ⟨H, s, fun z => -(π / 2) * (z ⬝ᵥ H.mulVec z), hH, hpos, ?_, ?_, ?_⟩
  · simp only [dotProduct, mulVec]
    fun_prop
  · rintro _ ⟨n, n', rfl⟩ _ ⟨p, p', rfl⟩
    refine ⟨p ⬝ᵥ n', ?_⟩
    have h1 : τ *ᵥ ofIntVec n + ofIntVec n' + (τ *ᵥ ofIntVec p + ofIntVec p')
        = τ *ᵥ ofIntVec (n + p) + ofIntVec (n' + p') := by
      rw [ofIntVec_add, ofIntVec_add, mulVec_add]; abel
    have h2 := im_form H hH (τ *ᵥ ofIntVec n + ofIntVec n') (τ *ᵥ ofIntVec p + ofIntVec p')
    rw [h1, hs, hs, hs]
    generalize ((((τ *ᵥ ofIntVec n + ofIntVec n') ⬝ᵥ
      H.mulVec (star (τ *ᵥ ofIntVec p + ofIntVec p'))).im : ℝ) : ℂ) = y at h2 ⊢
    have h4 : (τ *ᵥ ofIntVec n + ofIntVec n') ⬝ᵥ ofIntVec p
        = ofIntVec p ⬝ᵥ (τ *ᵥ ofIntVec n) + ((p ⬝ᵥ n' : ℤ) : ℂ) := by
      rw [dotProduct_comm, dotProduct_add, hcast]
    have h5 : (τ *ᵥ ofIntVec p + ofIntVec p') ⬝ᵥ ofIntVec n
        = ofIntVec p ⬝ᵥ (τ *ᵥ ofIntVec n) + ((n ⬝ᵥ p' : ℤ) : ℂ) := by
      rw [dotProduct_comm, dotProduct_add, hcast, dot_symm τ hτ.1]
    rw [hst, hst, dotProduct_sub, dotProduct_sub, dot_symm H hS, dotProduct_smul, dotProduct_smul,
      h4, h5, smul_eq_mul, smul_eq_mul] at h2
    have h3 : y = ((n ⬝ᵥ p' : ℤ) : ℂ) - ((p ⬝ᵥ n' : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero (α := ℂ)) I_ne_zero)
      linear_combination h2
    rw [h3, add_dotProduct, dotProduct_add, dotProduct_add]
    push_cast
    ring
  · rintro n n' l z hl
    have h1 := hst n n'
    have h2 := hs n n'
    have h3 : l ⬝ᵥ ofIntVec n = ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) + ofIntVec n ⬝ᵥ ofIntVec n' := by
      rw [dotProduct_comm, hl, dotProduct_add]
    rw [← hl] at h1 h2
    rw [h1, h2, hcast]
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, mulVec_add, dotProduct_add,
      add_dotProduct, h3, dot_symm H hS l z, dotProduct_comm z (ofIntVec n)]
    ring
end GlobalTheory.ThetaComplement
