-- Prove2me | solution 1 for GlobalTheory.bijective_algebraMap_of_subsingleton_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:22:15.347569+00:00
-- url     : https://prove2.me/submissions/ab23c35c-e7cc-41e6-9525-a887140fc4c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R A : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing A] [IsReduced A] [Nontrivial A] [Algebra R A]
    [Algebra.IsIntegral R A]
    (hgen : ∀ P : Ideal A, P.IsPrime → ∃ Q : Ideal A, Q.IsPrime ∧ Q ≤ P ∧
      Q.comap (algebraMap R A) = ⊥)
    (huniq : ∀ σ τ : A →ₐ[R] AlgebraicClosure (FractionRing R), σ = τ) :
    Function.Bijective (algebraMap R A) := by
  let K := FractionRing R
  let L := AlgebraicClosure K
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hRL
  haveI : Module.IsTorsionFree R L := FaithfulSMul.to_isTorsionFree _ _
  have hex : ∀ Q : Ideal A, Q.IsPrime → Q.comap (algebraMap R A) = ⊥ →
      ∃ σ : A →ₐ[R] L, RingHom.ker σ = Q := by
    intro Q hQ hQ0
    have hinj : Function.Injective (algebraMap R (A ⧸ Q)) := by
      rw [injective_iff_map_eq_zero]
      intro r hr
      have : r ∈ Q.comap (algebraMap R A) := by
        rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
        exact hr
      rwa [hQ0, Ideal.mem_bot] at this
    haveI : FaithfulSMul R (A ⧸ Q) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    haveI : Module.IsTorsionFree R (A ⧸ Q) := FaithfulSMul.to_isTorsionFree R _
    let σ₀ : (A ⧸ Q) →ₐ[R] L := IsAlgClosed.lift
    have h₀ : Function.Injective σ₀ := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h
      obtain ⟨r, hr, c, hc⟩ := (Algebra.IsIntegral.isIntegral (R := R) a).isAlgebraic.exists_nonzero_dvd
        (mem_nonZeroDivisors_of_ne_zero h)
      apply hr
      apply hRL
      rw [map_zero, ← σ₀.commutes, hc, map_mul, ha, zero_mul]
    refine ⟨σ₀.comp (Ideal.Quotient.mkₐ R Q), ?_⟩
    ext a
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff σ₀ h₀
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  obtain ⟨Q₀, hQ₀, -, hQ₀0⟩ := hgen M hM.isPrime
  obtain ⟨σ, -⟩ := hex Q₀ hQ₀ hQ₀0
  have hσ : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply IsNilpotent.eq_zero
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    intro P hP
    obtain ⟨Q, hQ, hQP, hQ0⟩ := hgen P hP
    obtain ⟨τ, hτ⟩ := hex Q hQ hQ0
    apply hQP
    rw [← hτ, huniq τ σ]
    exact ha
  constructor
  · intro r s h
    apply hRL
    rw [← σ.commutes, ← σ.commutes, h]
  · intro a
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (σ a)).2 fun g =>
      DFunLike.congr_fun (huniq ((g.toAlgHom.restrictScalars R).comp σ) σ) a
    have hint : IsIntegral R k := by
      rw [← isIntegral_algebraMap_iff (algebraMap K L).injective, hk]
      exact (Algebra.IsIntegral.isIntegral (R := R) a).map σ
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨r, hσ ?_⟩
    rw [σ.commutes, ← hk, ← hr, ← IsScalarTower.algebraMap_apply]
end GlobalTheory
