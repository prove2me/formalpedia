-- Prove2me | solution 1 for GlobalTheory.SmoothPointFamily.exists_basis_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:53:35.440424+00:00
-- url     : https://prove2.me/submissions/17598aa3-66a6-43b3-9b2a-140ca4aa8fec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsHolomorphicFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory GlobalTheory.SmoothPointFamily
open KaehlerDifferential
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory.SmoothPointFamily
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S) (m : ℕ) (s : Fin m → S)
      (b : Module.Basis (Fin m) (Localization.Away g) Ω[Localization.Away g⁄R]),
      g ∉ p ∧ ∀ i, b i = D R (Localization.Away g) (algebraMap S _ (s i)) := by
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)
  let e : (κ →₀ S) →ₗ[S] Ω[S⁄R] :=
    Finsupp.linearCombination S fun i : κ ↦ D R S (a i)
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[Localization.AtPrime p⁄R] := map R R S (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb]
  have heₚ : Function.Bijective eₚ := this ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] :=
    map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  obtain ⟨m, ⟨u⟩⟩ := Finite.exists_equiv_fin κ
  let b' : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R] :=
    .ofRepr (LinearEquiv.ofBijective eₜ' h).symm
  have hb' : ∀ i, b' i = D R (Localization.Away g) (algebraMap S _ (a i)) := fun i => by
    simp +zetaDelta [IsLocalizedModule.map_linearCombination]
  exact ⟨g, m, fun i => a (u.symm i), b'.reindex u, hg, fun i => by
    rw [Module.Basis.reindex_apply, hb']⟩
end GlobalTheory.SmoothPointFamily
