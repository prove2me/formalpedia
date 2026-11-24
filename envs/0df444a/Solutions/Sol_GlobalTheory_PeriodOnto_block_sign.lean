-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.block_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:43.300277+00:00
-- url     : https://prove2.me/submissions/e723cb14-ab05-4e22-b123-12743c92f647

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Theorems.Thm_GlobalTheory_PeriodOnto_comm_sgnMat_iff
import Theorems.Thm_GlobalTheory_PeriodOnto_blockOf_ofBlock
import Theorems.Thm_GlobalTheory_PeriodOnto_I_smul_ofBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ)
variable {Λ : Type} (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
  (e : ι → Λ → Fin r → ℂ) (M : ι → Matrix (Fin r) (Fin r) ℂ)
  (hM : ∀ v t, blockOf idx q t (P v) = M t *ᵥ e t v)
namespace GlobalTheory.PeriodOnto
theorem _root_.solution (A : ι → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ t, (A t).IsHermitian) (s : ι → ℝ)
    (hs : ∀ t, 0 < s t) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (h : ∀ z z', (hermForm Hm z z').im =
      ∑ t, -2 * s t * (blockOf idx q t z ⬝ᵥ A t *ᵥ star (blockOf idx q t z')).im) (t : ι) :
    sgnMat r q * A t = A t * sgnMat r q ∧ (sgnMat r q * A t).PosDef := by
  classical
  have h1 : ∀ w w', (hermForm Hm (ofBlock idx q t w) (ofBlock idx q t w')).im =
      -2 * s t * (w ⬝ᵥ A t *ᵥ star w').im := by
    intro w w'
    rw [h, Finset.sum_eq_single t]
    · simp [blockOf_ofBlock]
    · intro b _ hb; simp [blockOf_ofBlock, hb]
    · simp
  have hI : ∀ z z' : Fin g → ℂ, hermForm Hm (Complex.I • z) (Complex.I • z') = hermForm Hm z z' := by
    intro z z'
    simp [hermForm, star_smul, mulVec_smul, mulVec_neg, ← mul_assoc]
  have hI' : ∀ z z' : Fin g → ℂ, (hermForm Hm (Complex.I • z) z').im = (hermForm Hm z z').re := by
    intro z z'
    simp [hermForm]
  have hc : sgnMat r q * A t = A t * sgnMat r q := by
    rw [comm_sgnMat_iff]
    intro a b hab
    have h2 : ∀ c : ℂ, (c * A t a b).im = 0 := by
      intro c
      have h3 := h1 (Pi.single a c) (Pi.single b 1)
      rw [← hI, I_smul_ofBlock, I_smul_ofBlock, h1] at h3
      have h4 := mul_left_cancel₀ (by have := hs t; linarith : -2 * s t ≠ 0) h3
      have h5 : star (Pi.single b 1 : Fin r → ℂ) = Pi.single b 1 := by
        rw [← Pi.single_star]; simp
      have h6 : ∀ (a : Fin r) (c : ℂ), sgnMat r q *ᵥ (Pi.single a c) =
          ((FD.sgn q a : ℝ) : ℂ) • Pi.single a c := by
        intro a c
        ext k
        by_cases hk : k = a <;> simp [sgnMat, mulVec_diagonal, hk]
      rw [h6, h6] at h4
      simp only [star_smul, h5, mulVec_smul, smul_dotProduct, dotProduct_smul, single_dotProduct,
        mulVec_single_one, FD.sgn] at h4
      by_cases ha : (a : ℕ) < q <;> by_cases hb : (b : ℕ) < q <;> simp [ha, hb] at hab h4 ⊢ <;>
        linarith
    apply Complex.ext
    · simpa using h2 Complex.I
    · simpa using h2 1
  have hS : (sgnMat r q).IsHermitian := by
    apply isHermitian_diagonal_of_self_adjoint
    ext a; simp
  have hH : (sgnMat r q * A t).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, hS.eq, (hA t).eq, hc]
  refine ⟨hc, PosDef.of_dotProduct_mulVec_pos hH fun u hu => ?_⟩
  have hz : ofBlock idx q t (star u) ≠ 0 := by
    intro h0
    have := blockOf_ofBlock idx q t t (star u)
    rw [h0] at this
    simp only [map_zero, if_true] at this
    exact hu (star_eq_zero.mp this.symm)
  have h2 := hpos _ hz
  rw [← hI', I_smul_ofBlock, h1] at h2
  have h3 : (sgnMat r q *ᵥ star u) ⬝ᵥ A t *ᵥ u = star u ⬝ᵥ (sgnMat r q * A t) *ᵥ u := by
    rw [← mulVec_mulVec]
    simp only [dotProduct, sgnMat, mulVec_diagonal]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [smul_dotProduct, star_star, h3] at h2
  refine Complex.pos_iff.mpr ⟨?_, (hH.im_star_dotProduct_mulVec_self u).symm⟩
  simp only [smul_eq_mul, neg_mul, Complex.neg_im, Complex.I_mul, mul_neg, neg_neg] at h2
  have := hs t
  by_contra hcon
  push Not at hcon
  nlinarith
end GlobalTheory.PeriodOnto
