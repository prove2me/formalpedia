-- Prove2me | solution 1 for GlobalTheory.degree_idealHilbertPoly_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:18:07.077547+00:00
-- url     : https://prove2.me/submissions/e4a9d32d-8b33-4206-872e-d4eee3ba5950

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_degree_le_of_eventually_eval_nat
import Theorems.Thm_GlobalTheory_eventually_finrank_quotPiece
import Theorems.Thm_GlobalTheory_eventually_idealHilbertPoly_nonneg
import Theorems.Thm_GlobalTheory_finrank_quotPiece_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
variable [Finite ι]
namespace GlobalTheory
theorem _root_.solution {I J : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    (hJ : J.IsHomogeneous (homogeneousSubmodule ι k)) (h : I ≤ J) :
    (idealHilbertPoly J).degree ≤ (idealHilbertPoly I).degree := by
  refine degree_le_of_eventually_eval_nat (eventually_idealHilbertPoly_nonneg hJ) ?_
  filter_upwards [eventually_finrank_quotPiece hI, eventually_finrank_quotPiece hJ] with n h1 h2
  have h3 := finrank_quotPiece_add I n
  have h4 := finrank_quotPiece_add J n
  have h5 : finrank k (I.restrictScalars k ⊓ homogeneousSubmodule ι k n : Submodule k _) ≤
      finrank k (J.restrictScalars k ⊓ homogeneousSubmodule ι k n : Submodule k _) :=
    Submodule.finrank_mono (inf_le_inf_right _ fun x hx => h hx)
  rw [← h1, ← h2]
  exact_mod_cast (by omega)
end GlobalTheory
