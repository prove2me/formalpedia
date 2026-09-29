-- Prove2me | solution 1 for IsNoetherianRing.exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ce5bad38-23f1-549e-8145-5eaa1c83db5c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsNoetherianRing_exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one

set_option autoImplicit false

namespace ConnLoc

open TopologicalSpace Topology

theorem isOpen_connectedComponent_of_noetherianSpace {X : Type} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by

  have key : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩, mem_irreducibleComponent⟩
      intro hsub
      exact hy (hsub mem_irreducibleComponent)
    · rintro ⟨Z, ⟨hZ, hnsub⟩, hyZ⟩ hyC
      apply hnsub
      have hZirr : IsIrreducible Z := hZ.1
      have hZconn : IsPreconnected Z := hZirr.2.isPreconnected
      have hZx : Z ⊆ connectedComponent y := hZconn.subset_connectedComponent hyZ
      first | rw [connectedComponent_eq hyC] at hZx | rw [← connectedComponent_eq hyC] at hZx
      exact hZx
  have hclosed : IsClosed (connectedComponent x)ᶜ := by
    rw [key]
    refine Set.Finite.isClosed_biUnion ?_ (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)
    exact NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)
  exact isClosed_compl_iff.mp hclosed

theorem isIdempotentElem_eq_zero_or_one_of_preconnectedSpace {S : Type} [CommRing S]
    [PreconnectedSpace (PrimeSpectrum S)] (x : S) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  have hclopen : IsClopen ((PrimeSpectrum.basicOpen x : Set (PrimeSpectrum S))) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨x, hx, rfl⟩
  rcases isClopen_iff.mp hclopen with h | h
  · left
    have hbot : PrimeSpectrum.basicOpen x = ⊥ := by
      apply TopologicalSpace.Opens.ext
      simpa using h
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff x).mp hbot
    cases n with
    | zero =>
      have h1 : (1 : S) = 0 := by simpa using hn
      calc x = x * 1 := (mul_one x).symm
        _ = 0 := by rw [h1, mul_zero]
    | succ m => rw [← hx.pow_succ_eq m]; exact hn
  · right
    have hunit : IsUnit x := by
      by_contra hnu
      obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hnu
      have : (⟨m, hm.isPrime⟩ : PrimeSpectrum S) ∈ (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum S)) := by
        rw [h]; trivial
      exact (PrimeSpectrum.mem_basicOpen x _).mp this hxm
    obtain ⟨u, rfl⟩ := hunit
    have := hx.eq

    have h2 : (u : S) * u * ↑u⁻¹ = u * ↑u⁻¹ := by rw [this]
    simpa [mul_assoc] using h2

theorem main (B : Type) [CommRing B] [IsNoetherianRing B] (𝔭 : Ideal B) [h𝔭 : 𝔭.IsPrime] :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔭 ∧
      ∀ x : Localization.Away e, IsIdempotentElem x → x = 0 ∨ x = 1 := by
  let P : PrimeSpectrum B := ⟨𝔭, h𝔭⟩
  have hclopen : IsClopen (connectedComponent P) :=
    ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_noetherianSpace P⟩
  obtain ⟨e, he, hC⟩ := PrimeSpectrum.isClopen_iff.mp hclopen
  refine ⟨e, he, ?_, ?_⟩
  · have hP : P ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum B)) := hC ▸ mem_connectedComponent
    exact (PrimeSpectrum.mem_basicOpen e P).mp hP
  ·
    have hrange : Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away e))) = connectedComponent P := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away e) e, hC]
    have hind : IsInducing (PrimeSpectrum.comap (algebraMap B (Localization.Away e))) :=
      (PrimeSpectrum.localization_comap_isEmbedding (Localization.Away e) (Submonoid.powers e)).isInducing
    have hpre : IsPreconnected (Set.univ : Set (PrimeSpectrum (Localization.Away e))) := by
      rw [← hind.isPreconnected_image, Set.image_univ, hrange]
      exact isConnected_connectedComponent.isPreconnected
    haveI : PreconnectedSpace (PrimeSpectrum (Localization.Away e)) := ⟨hpre⟩
    intro x hx
    exact isIdempotentElem_eq_zero_or_one_of_preconnectedSpace x hx

end ConnLoc

theorem solution
    (B : Type) [CommRing B] [IsNoetherianRing B] (𝔭 : Ideal B) [𝔭.IsPrime] :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔭 ∧
      ∀ x : Localization.Away e, IsIdempotentElem x → x = 0 ∨ x = 1 :=
  ConnLoc.main B 𝔭

end S_IsNoetherianRing_exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one
end P2MW
export P2MW.S_IsNoetherianRing_exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one (solution)
