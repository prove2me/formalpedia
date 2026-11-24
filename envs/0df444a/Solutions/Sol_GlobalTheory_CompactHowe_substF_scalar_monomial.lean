-- Prove2me | solution 1 for GlobalTheory.CompactHowe.substF_scalar_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:06:20.103468+00:00
-- url     : https://prove2.me/submissions/1159556c-9cc1-4dfc-b609-25d9e8f0a77e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionScalarMonomial
import Theorems.Thm_GlobalTheory_CompactHowe_substF_scalar_X
import Theorems.Thm_GlobalTheory_CompactHowe_mapDomain_fst_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe
namespace GlobalTheory.CompactHowe
theorem _root_.solution {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow, substF_scalar_X, mul_pow, Finset.prod_mul_distrib]
  rw [mapDomain_fst_apply, smul_eq_C_mul, ← Finset.prod_pow_eq_pow_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← map_pow]
  split_ifs <;> simp
end GlobalTheory.CompactHowe
