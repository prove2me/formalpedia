-- Prove2me | solution 1 for GlobalTheory.fibre_dense_affine_chart_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:48:51.444866+00:00
-- url     : https://prove2.me/submissions/276b4182-1d6a-4f54-9e0a-76463c46e09f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreDenseAffineChartPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens) (U : X.Opens) (V : T.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : U ≤ p ⁻¹ᵁ V),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) →
    ∀ q : PrimeSpectrum Γ(X, U), q ∈ closure ({P : PrimeSpectrum Γ(X, U) | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (p.appLE V U e).hom ⁻¹' {PrimeSpectrum.comap (p.appLE V U e).hom q}) := by
  intro X T p W U V hU hV e hW b hb q
  set f := hU.fromSpec with hf
  have hemb : IsOpenEmbedding f := f.isOpenEmbedding

  have hmemU : ∀ P : PrimeSpectrum Γ(X, U), f P ∈ U := fun P => hU.range_fromSpec.le ⟨P, rfl⟩
  have hprime : ∀ P : PrimeSpectrum Γ(X, U), hU.primeIdealOf ⟨f P, hmemU P⟩ = P := fun P =>
    hemb.injective (hU.fromSpec_primeIdealOf _)
  have hcomap : ∀ P : PrimeSpectrum Γ(X, U),
      PrimeSpectrum.comap (p.appLE V U e).hom P = hV.primeIdealOf ⟨p (f P), e (hmemU P)⟩ := by
    intro P
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := p) V hV U hU e (hmemU P)
    rw [hprime P] at this
    exact this
  set A : Set X := (W : Set X) ∩ p ⁻¹' {p (f q)} with hA
  have hq : q ∈ closure (f ⁻¹' A) := by
    rw [← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]
    exact hW (f q)
  refine closure_mono ?_ hq
  intro P hP
  obtain ⟨hPW, hPp⟩ := hP
  refine ⟨?_, ?_⟩
  · let _ : Algebra Γ(X, U) (X.presheaf.stalk (f P)) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨f P, hmemU P⟩
    haveI hloc : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (f P)) := hU.isLocalization_stalk' P (hmemU P)
    have h0 : algebraMap Γ(X, U) (X.presheaf.stalk (f P)) b = 0 := hb (f P) (hmemU P) hPW
    obtain ⟨⟨s, hs⟩, hsb⟩ := (IsLocalization.map_eq_zero_iff P.asIdeal.primeCompl _ b).mp h0
    exact ⟨s, hs, hsb⟩
  · show PrimeSpectrum.comap (p.appLE V U e).hom P = PrimeSpectrum.comap (p.appLE V U e).hom q
    rw [hcomap P, hcomap q]
    have : p (f P) = p (f q) := hPp
    congr 2
end GlobalTheory
