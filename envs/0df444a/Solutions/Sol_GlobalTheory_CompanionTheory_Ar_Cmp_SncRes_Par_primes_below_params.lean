-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:51:08.880539+00:00
-- url     : https://prove2.me/submissions/6407bdd8-b9e9-43c5-ba74-87bb19fc7012

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_PrimesBelowParams
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_algebraMap_locRing_eq_zero_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_map_ptIdeal_eq_maximalIdeal
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_chPrime_le_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isUnit_algebraMap_locRing_iff
import Theorems.Thm_ReciprocityTheory_AnForm_R_isDomain_of_isRegularLocalRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_regular_params
import Theorems.Thm_ReciprocityTheory_AnForm_R_regular_params_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages GlobalTheory.CompanionTheory.Ar.Cmp
variable {m : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
theorem _root_.solution : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∀ i ∈ Jf, (SncRes.Par.chPrime I t (r i)).IsPrime ∧ I ≤ SncRes.Par.chPrime I t (r i) ∧ SncRes.Par.chPrime I t (r i) ≤ ptIdeal t ∧ Dc ≤ SncRes.Par.chPrime I t (r i) ∧ r i ∈ SncRes.Par.chPrime I t (r i) ∧ (∀ j ∈ Jf, j ≠ i → r j ∉ SncRes.Par.chPrime I t (r i)) ∧ ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → r i ∈ 𝔮 → SncRes.Par.chPrime I t (r i) ≤ 𝔮 := by
  intro m e I Dc t r Jf hIDc hI hreg hdim hspan hDc i hi
  haveI := hreg
  haveI : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing
  have hmax := map_ptIdeal_eq_maximalIdeal hI
  have hspan' : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      IsLocalRing.maximalIdeal (locRing I t) := hspan.trans hmax
  have hprime : ∀ l, Prime (algebraMap _ (locRing I t) (r l)) :=
    prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm
  have hnassoc := (regular_params_spec (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm).2
  have hIt : I ≤ ptIdeal t := fun h hh => RingHom.mem_ker.mpr (hI h hh)
  have hRi : r i ∈ chPrime I t (r i) := Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
  have hle : chPrime I t (r i) ≤ ptIdeal t := by
    intro g hg
    have hg' : algebraMap _ (locRing I t) g ∈ Ideal.span {algebraMap _ (locRing I t) (r i)} :=
      Ideal.mem_comap.mp hg
    have hsub : Ideal.span {algebraMap _ (locRing I t) (r i)} ≤ IsLocalRing.maximalIdeal (locRing I t) := by
      rw [Ideal.span_singleton_le_iff_mem, ← hspan']
      exact Ideal.subset_span ⟨i, rfl⟩
    have hnu := (IsLocalRing.mem_maximalIdeal _).mp (hsub hg')
    refine RingHom.mem_ker.mpr ?_
    by_contra hne
    exact hnu ((isUnit_algebraMap_locRing_iff I t hI g).mpr hne)
  have hpr : (chPrime I t (r i)).IsPrime := by
    haveI : (Ideal.span {algebraMap _ (locRing I t) (r i)}).IsPrime :=
      (Ideal.span_singleton_prime (hprime i).ne_zero).mpr (hprime i)
    exact Ideal.comap_isPrime _ _
  have hIle : I ≤ chPrime I t (r i) := by
    intro h hh
    refine Ideal.mem_comap.mpr ?_
    rw [algebraMap_locRing_eq_zero_of_mem t hh]
    exact Ideal.zero_mem _
  refine ⟨hpr, hIle, hle, (hDc _ hpr hIle hle).mpr ⟨i, hi, hRi⟩, hRi, ?_, ?_⟩
  · intro j _ hji hj
    have hd : algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) (r j) :=
      Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hj)
    exact hnassoc i j (Ne.symm hji) ((hprime i).associated_of_dvd (hprime j) hd)
  · intro 𝔮 h𝔮 hI𝔮 h𝔮t hr
    exact chPrime_le_of_mem h𝔮 hI𝔮 h𝔮t hr
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
