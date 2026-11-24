-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Gal.localEuler_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:30.684803+00:00
-- url     : https://prove2.me/submissions/4f39dffd-e75d-4c6d-aeff-53ca256a4a09

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalEulerPlaces
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Gal
namespace GlobalTheory.CompanionTheory.Gal
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), LocalEulerChar → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, (((l : ℕ) : 𝓞 F) ∈ v.1.asIdeal → Nat.card (H1 (ρ.comp (locFam S Av v))) = Nat.card (H0 (ρ.comp (locFam S Av v))) * Nat.card (H2 (ρ.comp (locFam S Av v))) * Nat.card M ^ locDeg v.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.1.asIdeal → Nat.card (H1 (ρ.comp (locFam S Av v))) = Nat.card (H0 (ρ.comp (locFam S Av v))) * Nat.card (H2 (ρ.comp (locFam S Av v)))) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ hE hr hA v
  exact hE F Ω l r M (Av v) (ρ.comp (locFam S Av v)) v.1 hr (hA v) (hρ.comp' (continuous_locFam S Av v))
end GlobalTheory.CompanionTheory.Gal
