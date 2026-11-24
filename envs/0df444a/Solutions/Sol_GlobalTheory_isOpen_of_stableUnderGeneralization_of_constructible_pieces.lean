-- Prove2me | solution 1 for GlobalTheory.isOpen_of_stableUnderGeneralization_of_constructible_pieces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:04:46.143673+00:00
-- url     : https://prove2.me/submissions/24cf5c79-bb64-4886-9e95-e8546480a062

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfConstructible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] (Z : Set (PrimeSpectrum A)), StableUnderGeneralization Z → (∀ p ∈ Z, ∃ (a : A) (I : Finset A), a ∉ p.asIdeal ∧ (∀ c ∈ I, c ∈ p.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → t ∈ Z) → IsOpen Z := by
  intro A _ Z hZ hpc
  rw [isOpen_iff_mem_nhds]
  intro p hp
  by_contra hn
  have hne : (nhds p ⊓ Filter.principal Zᶜ).NeBot := by
    rw [Filter.neBot_iff, Ne, Filter.inf_principal_eq_bot, compl_compl]
    exact hn
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (nhds p ⊓ Filter.principal Zᶜ)
  have hU1 : (U : Filter (PrimeSpectrum A)) ≤ nhds p := hU.trans inf_le_left
  have hU2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), t ∉ Z :=
    Filter.le_principal_iff.1 (hU.trans inf_le_right)
  have hle : ultrafilterPrime U ≤ p := by
    intro c hc
    by_contra hcp
    have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∈ t.asIdeal := hc
    have h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∉ t.asIdeal :=
      hU1 ((PrimeSpectrum.basicOpen c).isOpen.mem_nhds hcp)
    obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
    exact ht2 ht1
  have hq : ultrafilterPrime U ∈ Z :=
    hZ ((PrimeSpectrum.le_iff_specializes _ _).1 hle |> fun h => by simpa using h) hp
  obtain ⟨a, I, ha, hI, hsub⟩ := hpc _ hq
  have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∉ t.asIdeal :=
    Ultrafilter.eventually_not.2 ha
  have h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), ∀ c ∈ I, c ∈ t.asIdeal :=
    (Filter.eventually_all_finset I).2 fun c hc => hI c hc
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((h1.and h2).and hU2).exists
  exact ht3 (hsub t ht1 ht2)
end GlobalTheory
