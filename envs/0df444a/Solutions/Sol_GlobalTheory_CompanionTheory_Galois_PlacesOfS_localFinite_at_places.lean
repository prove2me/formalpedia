-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:27.344796+00:00
-- url     : https://prove2.me/submissions/2979dc91-788f-4696-b4ae-fa8b9934a27b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDual
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Galois GlobalTheory.CompanionTheory.Galois.PlacesOfS
namespace GlobalTheory.CompanionTheory.Galois.PlacesOfS
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, Finite (H0 (ρ.comp (locFam S Av v))) ∧ Finite (H1 (ρ.comp (locFam S Av v))) ∧ Finite (H2 (ρ.comp (locFam S Av v))) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ hF hr hA v
  obtain ⟨h0, h1, h2, -⟩ := hF F Ω l r M (Av v) (ρ.comp (locFam S Av v)) v.1 hr (hA v)
    (hρ.comp' (continuous_locFam S Av v))
  exact ⟨h0, h1, h2⟩
end GlobalTheory.CompanionTheory.Galois.PlacesOfS
