-- Prove2me | solution 1 for GlobalTheory.NoetherInt.exists_coeff_map_eq_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:35.737062+00:00
-- url     : https://prove2.me/submissions/ffcfc3eb-2787-48bf-a482-8d46cce060b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
import Theorems.Thm_GlobalTheory_NoetherInt_map_shear
import Theorems.Thm_GlobalTheory_NoetherInt_map_finSuccEquiv
import Theorems.Thm_GlobalTheory_NoetherInt_shear_leadingCoeff_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open MvPolynomial
namespace GlobalTheory.NoetherInt
theorem _root_.solution {K : Type*} [Field K] {n : ℕ} (φ : ℤ →+* K)
    (g : MvPolynomial (Fin (n + 1)) ℤ) (hg : MvPolynomial.map φ g ≠ 0) :
    ∃ (u k : ℕ) (a : K), a ≠ 0 ∧
      MvPolynomial.map φ ((finSuccEquiv ℤ n (shear ℤ n u g)).coeff k) = MvPolynomial.C a := by
  set f := MvPolynomial.map φ g with hf
  have hU := shear_leadingCoeff_isUnit f hg
  obtain ⟨a, ha, hE⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hU
  refine ⟨2 + f.totalDegree, (finSuccEquiv K n (shear K n (2 + f.totalDegree) f)).natDegree, a,
    ha.ne_zero, ?_⟩
  rw [← Polynomial.coeff_map, map_finSuccEquiv, map_shear, ← hf]
  exact hE
end GlobalTheory.NoetherInt
