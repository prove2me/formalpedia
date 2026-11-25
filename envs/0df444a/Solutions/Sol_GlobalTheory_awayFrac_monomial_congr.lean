-- Prove2me | solution 1 for GlobalTheory.awayFrac_monomial_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:12.914304+00:00
-- url     : https://prove2.me/submissions/8e742e7c-3a1f-4bd1-8c41-5d1a31380473

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LinearIndependentLaurentMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanLaurentMonomialEqHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Theorems.Thm_GlobalTheory_exists_xProd_pow_smul_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} [DecidableEq ι] (R : Type) [CommRing R]
    (s : Finset ι) (a : ι → ℤ) {k j : ℕ} {m m' : ι →₀ ℕ}
    (hm : ∀ i, (m i : ℤ) = a i + if i ∈ s then (k : ℤ) else 0)
    (hm' : ∀ i, (m' i : ℤ) = a i + if i ∈ s then (j : ℤ) else 0) :
    awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1) =
      awayFrac (MvPolynomial ι R) (xProd R s) j (monomial m' 1) := by
  refine awayFrac_eq_iff.2 ⟨0, ?_⟩
  obtain ⟨u, hu, eu⟩ := exists_xProd_pow_smul_monomial R s (0 + j) m
  obtain ⟨w, hw, ew⟩ := exists_xProd_pow_smul_monomial R s (0 + k) m'
  rw [eu, ew]
  congr 2
  ext i
  have h1 := hu i
  have h2 := hw i
  have h3 := hm i
  have h4 := hm' i
  split_ifs at h1 h2 h3 h4 <;> omega
end GlobalTheory
