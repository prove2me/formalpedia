-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.isVBOn_dual_and_bidual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:50:57.602248+00:00
-- url     : https://prove2.me/submissions/8cbcf591-665e-44cf-b144-e4197a4a6ac8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LatDual_mem_span_basis_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LatDual_dual_eq_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open LatDual
namespace GlobalTheory.CompanionTheory.Ar
namespace Lat
theorem _root_.solution :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ), L.IsVBOn T r ⊤ → L.dual.IsVBOn T r ⊤ ∧ ∀ p ∈ T, ∀ e : E, e ∈ L p ↔ ∀ w ∈ L.dual p, w e ∈ regAt ξ p := by
  intro X Ω _ ξ E _ _ L T r hL
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨U, hpU, b, hspan, hfr⟩ := hL p hp
    obtain ⟨hli, -⟩ := hfr p hp hpU
    obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin r) Ω E, ⇑B = b :=
      ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk hli _⟩
    refine ⟨U, hpU, ⇑B.dualBasis, B.dualBasis.span_eq, ?_⟩
    intro q hq hqU
    obtain ⟨-, hLq⟩ := hfr q hq hqU
    refine And.intro B.dualBasis.linearIndependent ?_
    exact LatDual.dual_eq_span L q B (by rw [hB]; exact hLq)
  · intro p hp e
    obtain ⟨U, hpU, b, hspan, hfr⟩ := hL p hp
    obtain ⟨hli, hLp0⟩ := hfr p hp hpU
    obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin r) Ω E, ⇑B = b :=
      ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk hli _⟩
    have hLp : L p = Submodule.span (regAt ξ p) (Set.range B) := by rw [hB]; exact hLp0
    constructor
    · intro he w hw
      exact hw e he
    · intro h
      rw [hLp, LatDual.mem_span_basis_iff p B e]
      intro i
      have hmem : B.dualBasis i ∈ L.dual p := by
        rw [LatDual.dual_eq_span L p B hLp]
        exact Submodule.subset_span ⟨i, rfl⟩
      have hi := h _ hmem
      rwa [Module.Basis.dualBasis_apply] at hi
end Lat
end GlobalTheory.CompanionTheory.Ar
