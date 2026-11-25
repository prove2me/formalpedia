-- Prove2me | solution 1 for GlobalTheory.ProjCut.exists_linear_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:25.739048+00:00
-- url     : https://prove2.me/submissions/58c8c5f7-f837-45e7-8da7-3ea23fc39aaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Theorems.Thm_GlobalTheory_ProjCut_isIntegral_of_projection
import Theorems.Thm_GlobalTheory_ProjCut_homogeneousComponent_aeval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_exists_cons_one_ne


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
open ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
variable {ι k : Type*} [Field k]
namespace GlobalTheory.ProjCut
theorem _root_.solution [Infinite k] {P : Ideal (MvPolynomial ι k)} (hP : P ≠ ⊤)
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (y : ι → k) (r : ℕ)
    (w : Fin r → MvPolynomial ι k) (hw : ∀ j, (w j).IsHomogeneous 1)
    (hy : ∀ j, eval y (w j) = 0)
    (hint : (aeval fun j => Ideal.Quotient.mk P (w j) :
      MvPolynomial (Fin r) k →ₐ[k] _).toRingHom.IsIntegral) :
    ∃ (s : ℕ) (z : Fin s → MvPolynomial ι k), (∀ j, (z j).IsHomogeneous 1) ∧
      (∀ j, eval y (z j) = 0) ∧
      (aeval fun j => Ideal.Quotient.mk P (z j) :
        MvPolynomial (Fin s) k →ₐ[k] _).toRingHom.IsIntegral ∧
      Function.Injective (aeval fun j => Ideal.Quotient.mk P (z j) :
        MvPolynomial (Fin s) k →ₐ[k] _) := by
  haveI : Nontrivial (MvPolynomial ι k ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP
  induction r with
  | zero =>
    refine ⟨0, w, hw, hy, hint, (injective_iff_map_eq_zero _).2 fun g hg => ?_⟩
    rw [eq_C_of_isEmpty g] at hg ⊢
    rw [algHom_C, map_eq_zero] at hg
    rw [hg, map_zero]
  | succ r ih =>
    by_cases hinj : Function.Injective (aeval fun j => Ideal.Quotient.mk P (w j) :
        MvPolynomial (Fin (r + 1)) k →ₐ[k] _)
    · exact ⟨r + 1, w, hw, hy, hint, hinj⟩
    rw [injective_iff_map_eq_zero] at hinj
    push Not at hinj
    obtain ⟨g, hg, hg0⟩ := hinj
    have e : ∀ g : MvPolynomial (Fin (r + 1)) k,
        aeval (fun j => Ideal.Quotient.mk P (w j)) g = Ideal.Quotient.mk P (aeval w g) :=
      fun g => (comp_aeval_apply w (Ideal.Quotient.mkₐ k P) g).symm
    obtain ⟨m, hm⟩ : ∃ m, homogeneousComponent m g ≠ 0 := by
      by_contra! hm
      apply hg0
      rw [← sum_homogeneousComponent g]
      exact Finset.sum_eq_zero fun m _ => hm m
    have hgm : aeval (fun j => Ideal.Quotient.mk P (w j)) (homogeneousComponent m g) = 0 := by
      rw [e, Ideal.Quotient.eq_zero_iff_mem] at hg ⊢
      rw [← homogeneousComponent_aeval w hw]
      exact homogeneousComponent_mem_of_mem hPh hg m
    obtain ⟨c, hc⟩ := exists_cons_one_ne (homogeneousComponent_isHomogeneous m g) hm
    let w' : Fin r → MvPolynomial ι k := fun j => w j.succ - C (c j) * w 0
    refine ih w' (fun j => (hw _).sub ((hw 0).C_mul _)) (fun j => by simp [w', hy]) ?_
    let φ : MvPolynomial (Fin r) k →ₐ[k] _ := aeval fun j => Ideal.Quotient.mk P (w' j)
    letI := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k (MvPolynomial (Fin r) k) (MvPolynomial ι k ⧸ P) :=
      IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
    refine (isIntegral_of_projection (R := MvPolynomial (Fin r) k) _ (Fin.cons 0 X) (Fin.cons 1 c)
      (Ideal.Quotient.mk P (w 0)) ?_ (homogeneousComponent_isHomogeneous m g) hgm hc hint).1
    intro j
    refine Fin.cases (by simp) (fun j => ?_) j
    have : algebraMap (MvPolynomial (Fin r) k) (MvPolynomial ι k ⧸ P) (X j) =
        Ideal.Quotient.mk P (w' j) := aeval_X _ _
    simp only [Fin.cons_succ, this, w', map_sub, map_mul]
    rw [← algebraMap_eq, Ideal.Quotient.mk_algebraMap]
    ring
end GlobalTheory.ProjCut
