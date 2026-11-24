-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.hasSum_ideal_of_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:26:07.476563+00:00
-- url     : https://prove2.me/submissions/1205b0ee-793f-46df-9c35-cb4c6cca1596

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_discr_pos
import Theorems.Thm_GlobalTheory_QuadraticZeta_hasSum_ideal
import Theorems.Thm_GlobalTheory_QuadraticZeta_exists_basis_of_image
import Theorems.Thm_GlobalTheory_QuadraticZeta_ne_zero_of_image
import Theorems.Thm_GlobalTheory_QuadraticZeta_absNorm_eq_of_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (hd : 4 < d) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {ω : ℂ} {τ : ℍ}
    (h : ∀ z, z ∈ σ '' 𝔞.1 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) {s : ℝ} (hs : 1 < s)
    (hE : Summable fun p : {p : ℤ × ℤ // p ≠ 0} =>
      τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s)) :
    HasSum (fun I : Ideal (𝓞 K) => open Classical in
      if ((I * 𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal
      then 2 * (Ideal.absNorm I : ℝ) ^ (-s) else 0)
      ((2 / √d) ^ s * ∑' p : {p : ℤ × ℤ // p ≠ 0},
        τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s)) := by
  have hω := ne_zero_of_image σ 𝔞.ne_zero h
  have hd0 := discr_pos h2 hD
  have hy := τ.im_pos
  obtain ⟨b, e0, e1⟩ := exists_basis_of_image σ hω h
  refine hasSum_ideal h2 hD σ hd 𝔞 (by linarith) ?_
  rw [← ((finTwoArrowEquiv ℤ).symm.trans b.equivFun.symm.toEquiv).hasSum_iff,
    ← hasSum_subtype_iff_of_support_subset (s := {p : ℤ × ℤ | p ≠ 0})]
  · refine (hE.hasSum.mul_left _).congr_fun fun p => ?_
    have e : σ (b.equivFun.symm ![p.1.1, p.1.2]) = ω * (p.1.1 * τ + p.1.2) := by
      simp [e0, e1]
      ring
    change (‖σ (b.equivFun.symm ![p.1.1, p.1.2])‖ ^ 2 / _) ^ (-s) = _
    rw [e, absNorm_eq_of_image h2 hD σ hω h, Real.rpow_neg_eq_inv_rpow,
      show 2 * s = ((2 : ℕ) : ℝ) * s by norm_num, Real.rpow_natCast_mul (norm_nonneg _),
      ← Real.div_rpow hy.le (by positivity), ← Real.mul_rpow (by positivity) (by positivity),
      norm_mul]
    congr 1
    have : ‖ω‖ ≠ 0 := by simpa using hω
    field_simp
  · intro p hp h0
    apply hp
    simp [h0, Real.zero_rpow (show -s ≠ 0 by linarith)]
end GlobalTheory.QuadraticZeta
