-- Prove2me | solution 1 for GlobalTheory.GermInterp.exists_sub_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:56:09.885909+00:00
-- url     : https://prove2.me/submissions/8c0b2d5e-f5e6-4495-b9da-5a31d4d3083a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsMaximalOfFinitePrimes
import Theorems.Thm_GlobalTheory_GermInterp_isMaximal_of_finite_primes
import Theorems.Thm_GlobalTheory_GermInterp_eq_of_comap_map_le
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
open GlobalTheory GlobalTheory.GermInterp
namespace GlobalTheory.GermInterp
theorem _root_.solution {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R)
    (hfin : {P : PrimeSpectrum R | I ≤ P.asIdeal}.Finite) {κ : Type*} [Finite κ] (P : κ → PrimeSpectrum R)
    (hinj : Function.Injective P) (hI : ∀ i, I ≤ (P i).asIdeal) (S : κ → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, IsLocalization.AtPrime (S i) (P i).asIdeal] (a : ∀ i, S i) :
    ∃ r : R, ∀ i, algebraMap R (S i) r - a i ∈ I.map (algebraMap R (S i)) := by
  have hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal :=
    fun Q hQ hIQ => isMaximal_of_finite_primes I hfin Q hQ hIQ
  let N : κ → Ideal R := fun i => (I.map (algebraMap R (S i))).comap (algebraMap R (S i))
  have key : ∀ i (M : Ideal R), M.IsMaximal → N i ≤ M → M = (P i).asIdeal :=
    fun i M hM hle => eq_of_comap_map_le I hmax (P i).asIdeal (hI i) (S i) M hM hle
  have hcop : Pairwise fun i j => IsCoprime (N i) (N j) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have e1 := key i M hM (le_trans le_sup_left hle)
    have e2 := key j M hM (le_trans le_sup_right hle)
    exact hij (hinj (PrimeSpectrum.ext (e1.symm.trans e2)))
  have hfrac : ∀ i, ∃ x : R, ∃ s : (P i).asIdeal.primeCompl, IsLocalization.mk' (S i) x s = a i := by
    intro i
    obtain ⟨⟨x, s⟩, h⟩ := IsLocalization.mk'_surjective (P i).asIdeal.primeCompl (a i)
    exact ⟨x, s, h⟩
  choose x s hxs using hfrac
  have hinv : ∀ i, ∃ t : R, (s i : R) * t - 1 ∈ N i := by
    intro i
    have hsup : N i ⊔ Ideal.span {(s i : R)} = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
      have e := key i M hM (le_trans le_sup_left hle)
      have hsM : (s i : R) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      rw [e] at hsM
      exact (s i).2 hsM
    have h1 : (1 : R) ∈ N i ⊔ Ideal.span {(s i : R)} := hsup ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine ⟨t, ?_⟩
    have e : (s i : R) * t - 1 = -y := by rw [← hyz]; ring
    rw [e]
    exact (N i).neg_mem hy
  choose t ht using hinv
  obtain ⟨z, hz⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun i => Ideal.Quotient.mk (N i) (x i * t i))
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨r, fun i => ?_⟩
  have hri : r - x i * t i ∈ N i := by
    have e := congrFun hz i
    rw [Ideal.quotientInfToPiQuotient_mk'] at e
    exact Ideal.Quotient.eq.1 e
  have h1 : algebraMap R (S i) r - algebraMap R (S i) (x i * t i) ∈ I.map (algebraMap R (S i)) := by
    rw [← map_sub]
    exact Ideal.mem_comap.1 hri
  have h2 : algebraMap R (S i) (x i * t i) - a i ∈ I.map (algebraMap R (S i)) := by
    rw [← hxs i]
    have hst : algebraMap R (S i) ((s i : R) * t i - 1) ∈ I.map (algebraMap R (S i)) :=
      Ideal.mem_comap.1 (ht i)
    have hspec := IsLocalization.mk'_spec (S i) (x i) (s i)
    have e : algebraMap R (S i) (x i * t i) - IsLocalization.mk' (S i) (x i) (s i) =
        IsLocalization.mk' (S i) (x i) (s i) * algebraMap R (S i) ((s i : R) * t i - 1) := by
      simp only [map_sub, map_mul, map_one]
      linear_combination (-(algebraMap R (S i) (t i))) * hspec
    rw [e]
    exact Ideal.mul_mem_left _ _ hst
  convert Ideal.add_mem _ h1 h2 using 1
  ring
end GlobalTheory.GermInterp
