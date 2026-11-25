-- Prove2me | solution 1 for GlobalTheory.exists_form_degree_le_of_isHilbertPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:09.993699+00:00
-- url     : https://prove2.me/submissions/3130a5a9-393b-4ebf-a881-6a57b5aa95e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Theorems.Thm_GlobalTheory_ProjCut_isInternal_quotPiece
import Theorems.Thm_GlobalTheory_ProjCut_mk_mul_mem_quotPiece
import Theorems.Thm_GlobalTheory_ProjCut_isIntegral_of_projection
import Theorems.Thm_GlobalTheory_ProjCut_exists_linear_normalisation
import Theorems.Thm_GlobalTheory_ProjCut_hilbertPoly_ne_zero
import Theorems.Thm_GlobalTheory_ProjCut_degree_lt_of_isIntegral
import Theorems.Thm_GlobalTheory_ProjCut_exists_monic_minimal
import Theorems.Thm_GlobalTheory_ProjCut_mul_choose_le_finrank
import Theorems.Thm_GlobalTheory_ProjCut_le_factorial_mul_leadingCoeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_coeff_cone
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_cone_homog


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
open MvPolynomial ProjCut ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι k : Type*} [Field k]
namespace GlobalTheory
theorem _root_.solution [Infinite k] [Finite ι]
    {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (hne : ∃ i, X i ∉ P)
    {H : Polynomial ℚ} (hH : IsHilbertPoly (quotPiece P) H)
    (y : ι → k) (hy : ∃ f ∈ P, eval y f ≠ 0) :
    ∃ (d : ℕ) (f : MvPolynomial ι k), f ∈ P ∧ f.IsHomogeneous d ∧
      (d : ℚ) ≤ H.natDegree.factorial * H.leadingCoeff ∧ eval y f ≠ 0 := by
  classical
  cases nonempty_fintype ι
  have hP : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  obtain ⟨g, hgP, hg⟩ := hy
  obtain ⟨m, hm⟩ : ∃ m, eval y (homogeneousComponent m g) ≠ 0 := by
    by_contra! hm
    apply hg
    rw [← sum_homogeneousComponent g, map_sum]
    exact Finset.sum_eq_zero fun m _ => hm m
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra! h0
    obtain rfl : y = 0 := funext h0
    have h1 := homogeneousComponent_mem_of_mem hPh hgP 0
    rw [homogeneousComponent_zero] at h1
    rw [eval_zero, constantCoeff_eq] at hg
    exact hP (P.eq_top_of_isUnit_mem h1 (hg.isUnit.map C))

  let ε := (Fintype.equivFin ι).symm
  let w : Fin (Fintype.card ι) → MvPolynomial ι k := fun j => X (ε j) - C (y (ε j) / y i) * X i
  have hint : (aeval fun j => Ideal.Quotient.mk P (w j) :
      MvPolynomial (Fin (Fintype.card ι)) k →ₐ[k] _).toRingHom.IsIntegral := by
    let φ : MvPolynomial (Fin (Fintype.card ι)) k →ₐ[k] _ :=
      aeval fun j => Ideal.Quotient.mk P (w j)
    letI := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k (MvPolynomial (Fin (Fintype.card ι)) k) (MvPolynomial ι k ⧸ P) :=
      IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
    have e : (aeval fun j => Ideal.Quotient.mk P (X j) : MvPolynomial ι k →ₐ[k] _) =
        Ideal.Quotient.mkₐ k P := by
      ext j; simp
    refine (isIntegral_of_projection (R := MvPolynomial (Fin (Fintype.card ι)) k)
      (fun j => Ideal.Quotient.mk P (X j)) (fun j => X (ε.symm j)) y
      (Ideal.Quotient.mk P (C (y i)⁻¹ * X i)) ?_ (homogeneousComponent_isHomogeneous m g) ?_ hm
      ?_).1
    · intro j
      have : algebraMap (MvPolynomial (Fin (Fintype.card ι)) k) (MvPolynomial ι k ⧸ P)
          (X (ε.symm j)) = Ideal.Quotient.mk P (w (ε.symm j)) := aeval_X _ _
      rw [this, ← Ideal.Quotient.mk_algebraMap, ← map_mul, ← map_add]
      congr 1
      simp only [w, Equiv.apply_symm_apply, div_eq_mul_inv, map_mul, algebraMap_eq]
      ring
    · rw [e]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (homogeneousComponent_mem_of_mem hPh hgP m)
    · rw [e]
      exact RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective k P)
  obtain ⟨s, z, hz, hzy, hzint, hzinj⟩ := exists_linear_normalisation hP hPh y _ w
    (fun j => (isHomogeneous_X _ _).sub ((isHomogeneous_X _ _).C_mul _))
    (fun j => by simp [w, hi]) hint
  letI := (isInternal_quotPiece hPh).chooseDecomposition
  have hdeg := degree_lt_of_isIntegral (quotPiece P) hH _
    (fun j n m hm => mk_mul_mem_quotPiece P (hz j) n hm) hzint
  obtain _ | e := s
  · exfalso
    exact hilbertPoly_ne_zero hne hH (by simpa using hdeg)
  have hdeg' : H.degree ≤ (e : ℕ) := by
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro n hn
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (hdeg.trans_le (by exact_mod_cast (by exact_mod_cast hn : e < n)))
  obtain ⟨p, hp, hp0, hpt, hind⟩ := exists_monic_minimal _ hzinj hzint (Ideal.Quotient.mk P (X i))
  have e1 : ∀ a : MvPolynomial (Fin (e + 1)) k,
      aeval (fun j => Ideal.Quotient.mk P (z j)) a = Ideal.Quotient.mk P (aeval z a) :=
    fun a => (comp_aeval_apply z (Ideal.Quotient.mkₐ k P) a).symm
  have hle := (le_factorial_mul_leadingCoeff hH hdeg' hp0
    (mul_choose_le_finrank P z hz (isHomogeneous_X k i) (fun a ha => hind a (by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum] at ha
      rw [← ha]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, ← e1]
      rfl)))).2
  let F : MvPolynomial ι k := p.eval₂ (aeval z : MvPolynomial (Fin (e + 1)) k →ₐ[k] _).toRingHom (X i)
  have hF : F ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂, ← hpt]
    congr 1
    exact RingHom.ext fun a => (e1 a).symm
  refine ⟨p.natDegree, homogeneousComponent p.natDegree F,
    homogeneousComponent_mem_of_mem hPh hF _, homogeneousComponent_isHomogeneous _ _, hle, ?_⟩
  have h1 := coeff_cone (R := k) y F p.natDegree
  have h2 : cone (R := k) y F =
      (p.map constantCoeff).comp (Polynomial.C (y i) * Polynomial.X) := by
    have h3 := Polynomial.hom_eval₂ p
      (aeval z : MvPolynomial (Fin (e + 1)) k →ₐ[k] _).toRingHom (cone (R := k) y).toRingHom (X i)
    rw [Polynomial.comp, Polynomial.eval₂_map]
    refine h3.trans ?_
    congr 1
    · ext a : 1
      · ext a : 1
        simp
      · have := cone_homog (R := k) y (hz a)
        simp [this, hzy]
    · simp [cone]
  rw [h2, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map, hp.coeff_natDegree, map_one,
    one_mul] at h1
  rw [← coe_aeval_eq_eval]
  exact h1 ▸ pow_ne_zero _ hi
end GlobalTheory
