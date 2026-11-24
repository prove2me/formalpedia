-- Prove2me | solution 1 for GlobalTheory.CycAway.dedekind_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:28:54.607077+00:00
-- url     : https://prove2.me/submissions/586557cb-96fc-4225-93e6-76c58252c8c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsLocalizationOfLeClosure
import Theorems.Thm_GlobalTheory_CycAway_isLocalization_of_le_closure

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
open GlobalTheory.SS
open GlobalTheory GlobalTheory.CycAway
open NumberField
namespace GlobalTheory.CycAway
theorem _root_.solution {Ω K : Type} [Field Ω] [CharZero Ω] [Field K] [CharZero K] {n a : ℕ} (hn : n.Prime)
    [IsCyclotomicExtension {n ^ a} ℚ K] (φ : K →+* Ω) {ζ : K} (hζ : IsPrimitiveRoot ζ (n ^ a)) :
    IsDedekindDomain (Subring.closure {φ ζ, (n : Ω)⁻¹}) ∧ Algebra.FiniteType ℤ (Subring.closure {φ ζ, (n : Ω)⁻¹}) := by
  haveI := Fact.mk hn
  haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  let io : 𝓞 K →+* Ω := φ.comp (algebraMap _ K)
  have hio : Function.Injective io := φ.injective.comp RingOfIntegers.coe_injective
  have hmem : ∀ x, io x ∈ T := by
    intro x
    obtain ⟨y, hy⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1
      (RingOfIntegers.isIntegral_coe x)
    have h1 : (y : K) ∈ Subring.closure ({ζ} : Set K) := by
      exact Algebra.mem_adjoin_iff.1 y.2 |> fun h => (Subring.closure_le.2 (by
        rintro _ (⟨r, rfl⟩ | h)
        · exact intCast_mem (Subring.closure ({ζ} : Set K)) r
        · exact Subring.subset_closure h)) h
    have h2 : Subring.closure ({ζ} : Set K) ≤ T.comap φ := by
      rw [Subring.closure_le]
      rintro _ rfl
      exact Subring.subset_closure (Or.inl rfl)
    have h3 : io x = φ y := congrArg φ hy.symm
    rw [h3]
    exact h2 h1
  letI : Algebra (𝓞 K) T := (io.codRestrict _ hmem).toAlgebra
  have hL : IsLocalization (Submonoid.powers (n : 𝓞 K)) T := by
    refine isLocalization_of_le_closure h0 _ _ (fun x y h => hio (congrArg (fun z : T => (z : Ω)) h))
      (Subring.subset_closure (Or.inr rfl)) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨hζ.toInteger, rfl⟩
    · exact Or.inr h
  have hn' : (n : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne_zero
  refine ⟨IsLocalization.isDedekindDomain _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn') _, ?_⟩
  have h1 : Algebra.FiniteType ℤ (𝓞 K) := inferInstance
  have h2 : Algebra.FiniteType (𝓞 K) T :=
    have := IsLocalization.Away.finitePresentation (S := T) (n : 𝓞 K)
    inferInstance
  exact h1.trans h2
end GlobalTheory.CycAway
