-- Prove2me | solution 1 for GlobalTheory.mvPolynomial_exists_content
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:46.842073+00:00
-- url     : https://prove2.me/submissions/2cbbadea-ad6f-4c7d-b5fa-f044e3e3683e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
import Theorems.Thm_GlobalTheory_valuationRing_exists_dvd_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] (g : ℕ)
    (F : MvPolynomial (Fin g) O) (hF : F ≠ 0) :
    ∃ (π : O) (F' : MvPolynomial (Fin g) O), F = MvPolynomial.C π * F' ∧
      F' ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) := by
  obtain ⟨i, hi, h⟩ := valuationRing_exists_dvd_all (fun m => F.coeff m) F.support
    (MvPolynomial.support_nonempty.2 hF)
  have hd : MvPolynomial.C (F.coeff i) ∣ F := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro m
    by_cases hm : m ∈ F.support
    · exact h m hm
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      exact dvd_zero _
  obtain ⟨F', hF'⟩ := hd
  refine ⟨F.coeff i, F', hF', fun hmem => ?_⟩
  have h1 := MvPolynomial.mem_map_C_iff.1 hmem i
  have h2 : F.coeff i = F.coeff i * F'.coeff i := by
    conv_lhs => rw [hF', MvPolynomial.coeff_C_mul]
  have h3 : F'.coeff i = 1 :=
    (mul_left_cancel₀ (MvPolynomial.mem_support_iff.1 hi) ((mul_one _).trans h2)).symm
  rw [h3] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
end GlobalTheory
