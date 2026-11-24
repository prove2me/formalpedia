-- Prove2me | solution 1 for GlobalTheory.HermSign.exists_diag_of_complexStructure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:03:02.878456+00:00
-- url     : https://prove2.me/submissions/0a112a72-6207-42bb-b246-43646bd903b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
import Theorems.Thm_GlobalTheory_HermSign_exists_diag_of_involution
import Theorems.Thm_GlobalTheory_HermSign_eq_of_re_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
namespace GlobalTheory.HermSign
theorem _root_.solution {r m n : ℕ} (hr : r = m + n)
    (G M : Matrix (Fin r) (Fin r) ℂ) (hG : G.IsHermitian) (s : ℝ) (ε : ℝ) (hε : ε * ε = 1)
    (hs : 0 < ε * s) (hM : M * M = -1)
    (hinv : ∀ u v : Fin r → ℂ, ((s * Complex.I) * ((M *ᵥ u) ⬝ᵥ G *ᵥ star (M *ᵥ v))).re =
      ((s * Complex.I) * (u ⬝ᵥ G *ᵥ star v)).re)
    (hpos : ∀ u : Fin r → ℂ, u ≠ 0 → 0 < ((s * Complex.I) * ((M *ᵥ u) ⬝ᵥ G *ᵥ star u)).re)
    (ht : ε * Complex.I * M.trace = (m : ℂ) - n) :
    ∃ N : Matrix (Fin r) (Fin r) ℂ, N.det ≠ 0 ∧
      Nᴴ * G * N = diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ) := by
  classical
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h; rw [Complex.ofReal_eq_zero] at h; simp [h] at hs
  have hεc : (ε : ℂ) * ε = 1 := by exact_mod_cast hε
  have hMt : Mᵀ * Mᵀ = -1 := by rw [← transpose_mul, hM, transpose_neg, transpose_one]
  have hform : ∀ u w : Fin r → ℂ, (M *ᵥ u) ⬝ᵥ G *ᵥ w = u ⬝ᵥ (Mᵀ * G) *ᵥ w := by
    intro u w
    rw [← mulVec_mulVec, dotProduct_mulVec u Mᵀ, vecMul_transpose]
  have hI : Mᵀ * G * Mᵀᴴ = G := by
    refine eq_of_re_form _ _ (s * Complex.I) (mul_ne_zero hs0 Complex.I_ne_zero) fun u v => ?_
    rw [← hinv u v, hform, star_mulVec, ← mulVec_mulVec _ _ Mᵀᴴ]
    congr 4
    rw [← mulVec_transpose]; rfl
  have hI2 : G * Mᵀᴴ = -(Mᵀ * G) := by
    calc G * Mᵀᴴ = -((Mᵀ * Mᵀ) * G * Mᵀᴴ) := by rw [hMt]; simp
      _ = -(Mᵀ * (Mᵀ * G * Mᵀᴴ)) := by simp only [mul_assoc]
      _ = _ := by rw [hI]
  refine exists_diag_of_involution hr G ((ε * Complex.I : ℂ) • Mᵀ) hG ?_ ?_ ?_
  · rw [smul_mul_smul_comm, hMt, show (ε * Complex.I : ℂ) * (ε * Complex.I) = -1 by
      linear_combination (Complex.I * Complex.I) * hεc + Complex.I_mul_I]
    simp
  · have hH : (((ε * Complex.I : ℂ) • Mᵀ) * G).IsHermitian := by
      unfold IsHermitian
      rw [smul_mul_assoc, conjTranspose_smul, conjTranspose_mul, hG.eq, hI2]
      simp
    refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have h1 := hpos (star x) (by simpa using hx)
    rw [hform, star_star] at h1
    rw [Complex.lt_def]
    refine ⟨?_, ?_⟩
    · rw [smul_mul_assoc, smul_mulVec, dotProduct_smul, smul_eq_mul]
      simp only [mul_assoc, Complex.re_ofReal_mul] at h1 ⊢
      rw [Complex.zero_re]
      by_contra hc
      push Not at hc
      have := mul_nonpos_of_nonneg_of_nonpos hs.le hc
      have e : ε * s * (ε * (Complex.I * star x ⬝ᵥ (Mᵀ * G) *ᵥ x).re) =
        (ε * ε) * (s * (Complex.I * star x ⬝ᵥ (Mᵀ * G) *ᵥ x).re) := by ring
      rw [e, hε] at this
      linarith
    · exact (hH.im_star_dotProduct_mulVec_self x).symm
  · rw [trace_smul, trace_transpose, smul_eq_mul, ht]
end GlobalTheory.HermSign
