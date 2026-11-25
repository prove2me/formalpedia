-- Prove2me | solution 1 for GlobalTheory.exists_ne_zero_forall_exists_two_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:36:11.030807+00:00
-- url     : https://prove2.me/submissions/b66f32d9-225e-4c0c-94c3-3a42208d5b60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Theorems.Thm_GlobalTheory_exists_ringHom_extend_of_isIntegral_of_injective

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
    [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
    (σ τ : A →ₐ[R] AlgebraicClosure (FractionRing R)) (hne : σ ≠ τ) :
    ∃ r : R, r ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (O : ValuationSubring Ω)
      (φ : R →+* O), φ r ≠ 0 → ∃ ψ ψ' : A →+* O, ψ.comp (algebraMap R A) = φ ∧
        ψ'.comp (algebraMap R A) = φ ∧ ψ ≠ ψ' := by
  let K := FractionRing R
  let L := AlgebraicClosure K
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  let B := integralClosure R L
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    fun r s h => hRL congr(($h).1)
  let c (ρ : A →ₐ[R] L) : A →ₐ[R] B :=
    ρ.codRestrict B fun a => (Algebra.IsIntegral.isIntegral (R := R) a).map ρ
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hne
  have hb : c σ a - c τ a ≠ 0 := fun h => ha congr(($(sub_eq_zero.mp h)).1)
  obtain ⟨r, hr, d, hd⟩ :=
    (Algebra.IsIntegral.isIntegral (R := R) (c σ a - c τ a)).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hb)
  refine ⟨r, hr, fun Ω _ _ O φ hφ => ?_⟩
  obtain ⟨χ, hχ⟩ := exists_ringHom_extend_of_isIntegral_of_injective (B := B) (O.subtype.comp φ)
  have hχ' (s : R) : χ (algebraMap R B s) = φ s := DFunLike.congr_fun hχ s
  have hmem (b : B) : χ b ∈ O := by
    have h₁ : IsIntegral O (χ b) :=
      (Algebra.IsIntegral.isIntegral (R := R) b).map_of_comp_eq φ χ hχ.symm
    obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.mp h₁
    exact ho ▸ o.2
  let χ' : B →+* O := χ.codRestrict O hmem
  have hcomp (ρ : A →ₐ[R] L) : (χ'.comp (c ρ).toRingHom).comp (algebraMap R A) = φ := by
    refine RingHom.ext fun s => Subtype.ext ?_
    exact (congrArg χ ((c ρ).commutes s)).trans (hχ' s)
  refine ⟨_, _, hcomp σ, hcomp τ, fun h => hφ (Subtype.ext ?_)⟩
  have h₂ : χ (c σ a) = χ (c τ a) := congr((($h) a).1)
  rw [← hχ', hd, map_mul, map_sub, h₂, sub_self, zero_mul]
  rfl
end GlobalTheory
