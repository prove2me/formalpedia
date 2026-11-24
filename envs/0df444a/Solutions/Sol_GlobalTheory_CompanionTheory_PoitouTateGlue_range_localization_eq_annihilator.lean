-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PoitouTateGlue.range_localization_eq_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:15.376157+00:00
-- url     : https://prove2.me/submissions/8b610521-6f47-47b4-a5b4-96aa423f7b88

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TateShafarevichDualityH1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PoitouTateGlue
namespace GlobalTheory.CompanionTheory.PoitouTateGlue
theorem _root_.solution (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ)
    (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
    (h : NineTermExact S Av μ j ρ hρ) :
    LinearMap.range (loc1 S Av ρ) =
      ⨅ y ∈ LinearMap.range (loc1 S Av (twDual μ ρ)), LinearMap.ker (sumPair S Av μ j ρ hρ y) := by
  obtain ⟨δ₁, δ₂, -, -, -, -, hex, -⟩ := h
  have key : ∀ z x, sumPair S Av μ j ρ hρ (loc1 S Av (twDual μ ρ) z) x =
      GlobalTheory.Published.PoitouTate.tr1 S Av μ j ρ hρ x z := by
    intro z x
    simp [sumPair, GlobalTheory.Published.PoitouTate.tr1, loc1, LinearMap.sum_apply]
  ext x
  rw [Submodule.mem_iInf]
  constructor
  · intro hx y
    rw [Submodule.mem_iInf]
    rintro ⟨z, rfl⟩
    rw [LinearMap.mem_ker, key, (hex x).mpr (LinearMap.mem_range.mp hx)]
    simp
  · intro hx
    obtain ⟨y, hy⟩ := (hex x).mp (LinearMap.ext fun z => by
      have hz := (Submodule.mem_iInf _).mp (hx (loc1 S Av (twDual μ ρ) z)) ⟨z, rfl⟩
      rw [LinearMap.mem_ker, key] at hz
      simpa using hz)
    exact ⟨y, hy⟩
end GlobalTheory.CompanionTheory.PoitouTateGlue
