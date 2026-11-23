-- Prove2me | solution 1 for GlobalTheory.le_idealOfVars_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:54.594037+00:00
-- url     : https://prove2.me/submissions/2941193d-05fc-4041-87aa-bde1623d0c58

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ : Type*}
namespace GlobalTheory
theorem _root_.solution {k : Type*} [Field k] {J : Ideal (MvPolynomial σ k)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ k)) (hJ' : J ≠ ⊤) : J ≤ idealOfVars σ k := by
  intro x hx
  rw [← pow_one (idealOfVars σ k), mem_pow_idealOfVars_iff']
  intro m hm
  have hm0 : m = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]; omega
  subst hm0
  by_contra hne
  have h0 := homogeneousComponent_mem_of_mem hJ hx 0
  rw [homogeneousComponent_zero] at h0
  exact hJ' (J.eq_top_of_isUnit_mem h0 ((Ne.isUnit hne).map C))
end GlobalTheory
