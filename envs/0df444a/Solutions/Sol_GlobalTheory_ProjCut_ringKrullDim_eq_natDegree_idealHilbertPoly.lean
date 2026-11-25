-- Prove2me | solution 1 for GlobalTheory.ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:05.40222+00:00
-- url     : https://prove2.me/submissions/89088459-9a9c-4cb1-811a-d8882a1316f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Theorems.Thm_GlobalTheory_ProjCut_isInternal_quotPiece
import Theorems.Thm_GlobalTheory_ProjCut_mk_mul_mem_quotPiece
import Theorems.Thm_GlobalTheory_ProjCut_exists_linear_normalisation
import Theorems.Thm_GlobalTheory_ProjCut_hilbertPoly_ne_zero
import Theorems.Thm_GlobalTheory_ProjCut_degree_lt_of_isIntegral
import Theorems.Thm_GlobalTheory_ProjCut_mul_choose_le_finrank
import Theorems.Thm_GlobalTheory_ProjCut_le_factorial_mul_leadingCoeff
import Theorems.Thm_GlobalTheory_isHilbertPoly_idealHilbertPoly
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_eq_of_isIntegral_of_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module
open GlobalTheory
open GlobalTheory.ProjCut
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι k : Type*} [Field k]
namespace GlobalTheory.ProjCut
theorem _root_.solution [Infinite k] [Finite ι]
    {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (hne : ∃ i, X i ∉ P) :
    ringKrullDim (MvPolynomial ι k ⧸ P) = ((idealHilbertPoly P).natDegree + 1 : ℕ) := by
  classical
  cases nonempty_fintype ι
  have hH := isHilbertPoly_idealHilbertPoly hPh
  let ε := (Fintype.equivFin ι).symm
  obtain ⟨s, z, hz, -, hzint, hzinj⟩ := exists_linear_normalisation
    (Ideal.IsPrime.ne_top ‹_›) hPh 0 _ (fun j => X (ε j))
    (fun j => isHomogeneous_X _ _) (fun j => by simp) (by
      refine RingHom.isIntegral_of_surjective _ fun x => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨rename ε.symm x, ?_⟩
      have : (aeval fun j => Ideal.Quotient.mk P (X (ε j)) :
          MvPolynomial (Fin (Fintype.card ι)) k →ₐ[k] _).comp (rename ε.symm) =
          Ideal.Quotient.mkₐ k P := by
        ext j; simp
      exact DFunLike.congr_fun this x)
  letI := (isInternal_quotPiece hPh).chooseDecomposition
  have hdeg := degree_lt_of_isIntegral (quotPiece P) hH _
    (fun j n m hm => mk_mul_mem_quotPiece P (hz j) n hm) hzint
  obtain _ | e := s
  · exfalso
    exact hilbertPoly_ne_zero hne hH (by simpa using hdeg)
  have hdeg' : (idealHilbertPoly P).degree ≤ (e : ℕ) := by
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro n hn
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (hdeg.trans_le (by exact_mod_cast (by exact_mod_cast hn : e < n)))
  obtain ⟨i, -⟩ := hne
  have he := (le_factorial_mul_leadingCoeff hH hdeg' one_pos
    (mul_choose_le_finrank P z hz (isHomogeneous_X k i) (fun a ha => by
      funext j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      refine (injective_iff_map_eq_zero _).1 hzinj _ ?_
      refine (comp_aeval_apply z (Ideal.Quotient.mkₐ k P) _).symm.trans ?_
      simpa [Ideal.Quotient.eq_zero_iff_mem] using ha))).1
  let φ : MvPolynomial (Fin (e + 1)) k →ₐ[k] _ := aeval fun j => Ideal.Quotient.mk P (z j)
  letI := φ.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin (e + 1)) k) (MvPolynomial ι k ⧸ P) := ⟨hzint⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective
    (A := MvPolynomial (Fin (e + 1)) k) hzinj, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, he]
  simp
end GlobalTheory.ProjCut
