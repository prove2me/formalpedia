-- Prove2me | solution 1 for GlobalTheory.coeff_sub_comp_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:06.787861+00:00
-- url     : https://prove2.me/submissions/a4d0f317-9900-44d3-ae11-f3d50a07c6a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter
open GlobalTheory
open DirectSum Module GradedHilbert
variable {k : Type*} [Field k] {M' M M'' : Type*} [AddCommGroup M'] [Module k M']
  [AddCommGroup M] [Module k M] [AddCommGroup M''] [Module k M'']
variable {ι : Type*} [Module (MvPolynomial ι k) M'] [IsScalarTower k (MvPolynomial ι k) M']
  [Module (MvPolynomial ι k) M] [IsScalarTower k (MvPolynomial ι k) M]
  [Module (MvPolynomial ι k) M''] [IsScalarTower k (MvPolynomial ι k) M'']
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Field K] (P : K[X]) (r : K) (e : ℕ)
    (hP : P.degree ≤ (e + 1 : ℕ)) :
    (P - P.comp (X - C r)).degree < (e + 1 : ℕ) ∧
      (P - P.comp (X - C r)).coeff e = r * (e + 1) * P.coeff (e + 1) := by
  have hQ : P = (P.comp (X - C r)).comp (X + C r) := by
    rw [comp_assoc]
    simp
  have hdeg : (P.comp (X - C r)).degree ≤ (e + 1 : ℕ) := by
    rw [sub_eq_add_neg, ← C_neg, ← taylor_apply, degree_taylor]
    exact hP
  have htop : (P.comp (X - C r)).coeff (e + 1) = P.coeff (e + 1) := by
    rw [sub_eq_add_neg, ← C_neg]
    exact coeff_comp_X_add_C_of_natDegree_le P (-r) (e + 1) (natDegree_le_iff_degree_le.mpr hP)
  have hdiff : P - P.comp (X - C r) = (P.comp (X - C r)).comp (X + C r) - P.comp (X - C r) := by
    rw [← hQ]
  rw [hdiff]
  exact ⟨degree_comp_X_add_C_sub_lt _ r (e + 1) hdeg,
    by rw [coeff_comp_X_add_C_sub _ r e hdeg, htop]⟩
end GlobalTheory
