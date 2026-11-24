-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrimeAvoid.exists_basicOpen_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:20.092443+00:00
-- url     : https://prove2.me/submissions/0b793d90-0c3d-4d7d-98b3-8386cab1b494

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteSetBasicOpenAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimeAvoid
namespace GlobalTheory.CompanionTheory.PrimeAvoid
theorem _root_.solution {X : Scheme.{0}} (U V₀ : X.Opens) (hU : IsAffineOpen U)
    (hV : V₀ ≤ U) (K : Set X) (hK : K.Finite) (hKV : K ⊆ V₀) :
    ∃ f : Γ(X, U), K ⊆ X.basicOpen f ∧ X.basicOpen f ≤ V₀ := by
  classical
  let W : Set (PrimeSpectrum Γ(X, U)) := hU.fromSpec ⁻¹' (V₀ : Set X)
  have hWo : IsOpen W := (hU.fromSpec ⁻¹ᵁ V₀).isOpen
  let I : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal Wᶜ
  let s : Set (Ideal Γ(X, U)) := PrimeSpectrum.asIdeal '' (hU.fromSpec ⁻¹' K)
  have hs : s.Finite := (hK.preimage hU.fromSpec.isOpenEmbedding.injective.injOn).image _
  have hnot : ¬ ((I : Set Γ(X, U)) ⊆ ⋃ P ∈ s, (P : Set Γ(X, U))) := by
    intro h
    obtain ⟨P, ⟨p, hpK, rfl⟩, hIp⟩ :=
      (Ideal.subset_union_prime_finite (f := fun P : Ideal Γ(X, U) => P) hs ⊥ ⊥
        (fun P hP _ _ => by obtain ⟨p, -, rfl⟩ := hP; exact p.isPrime)).1 h
    have hpW : p ∈ W := hKV hpK
    have hcl : p ∈ closure Wᶜ := by
      rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact (PrimeSpectrum.mem_zeroLocus _ _).2 hIp
    rw [hWo.isClosed_compl.closure_eq] at hcl
    exact hcl hpW
  obtain ⟨g, hgI, hgs⟩ := Set.not_subset.1 hnot
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact hV (hKV hx)
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen g p).2 fun hg => hgs (Set.mem_biUnion ⟨p, hx, rfl⟩ hg)
    exact hp
  · intro x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact X.basicOpen_le g hx
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := hx
    rw [hU.fromSpec_preimage_basicOpen] at hp
    have hp' := (PrimeSpectrum.mem_basicOpen g p).1 hp
    by_contra hpV
    exact hp' ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hgI p hpV)
end GlobalTheory.CompanionTheory.PrimeAvoid
