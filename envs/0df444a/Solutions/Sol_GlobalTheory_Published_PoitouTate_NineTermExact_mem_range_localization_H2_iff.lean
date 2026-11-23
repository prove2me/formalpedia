-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTate.NineTermExact.mem_range_localization_H2_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:00.80342+00:00
-- url     : https://prove2.me/submissions/970486ae-e60a-4d3b-8ece-e0f2ad740c06

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Theorems.Thm_GlobalTheory_Published_PoitouTate_poitouTateNineTerm_transgressionTwo_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.PoitouTate
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
variable (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
variable {S Av μ j ρ}
namespace GlobalTheory.Published.PoitouTate
namespace NineTermExact
theorem _root_.solution {hρ : ContAction ρ} (h : NineTermExact S Av μ j ρ hρ)
    (x : ∀ v : S, H2 (ρ.comp (locFam S Av v))) :
    x ∈ LinearMap.range (loc2 S Av ρ) ↔ ∀ y : H0 (twDual μ ρ),
      ∑ v : S, j v (cup20 μ ρ (locFam S Av v) (x v) (resH0 (twDual μ ρ) (locFam S Av v) y)) = 0 := by
  obtain ⟨δ₁, δ₂, -, -, -, -, -, -, -, h8, -⟩ := h
  rw [LinearMap.mem_range, ← Set.mem_range, ← h8 x, LinearMap.ext_iff]
  simp only [LinearMap.zero_apply, poitouTateNineTerm_transgressionTwo_apply]
end NineTermExact
end GlobalTheory.Published.PoitouTate
