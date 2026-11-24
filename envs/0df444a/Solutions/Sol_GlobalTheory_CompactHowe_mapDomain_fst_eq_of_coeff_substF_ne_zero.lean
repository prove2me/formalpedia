-- Prove2me | solution 1 for GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:11.362926+00:00
-- url     : https://prove2.me/submissions/a1927548-c1fa-4ae0-9dfb-78269a660a94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
import Theorems.Thm_GlobalTheory_CompactHowe_weight_fst_eq_mapDomain
import Theorems.Thm_GlobalTheory_CompactHowe_substF_X_isWeightedHomogeneous

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
theorem _root_.solution {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ)
    (hk : MvPolynomial.coeff k' (substF h g (MvPolynomial.monomial k 1)) ≠ 0) :
    Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  have key : IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (MvPolynomial.monomial k 1)) (Finsupp.mapDomain Prod.fst k) := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, ← weight_fst_eq_mapDomain, Finsupp.weight_apply,
      Finsupp.sum]
    refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
    rw [map_pow]
    exact (substF_X_isWeightedHomogeneous h g p).pow (k p)
  rw [← weight_fst_eq_mapDomain]
  exact key hk
end GlobalTheory.CompactHowe
