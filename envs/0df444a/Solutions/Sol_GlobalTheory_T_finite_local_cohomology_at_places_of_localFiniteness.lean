-- Prove2me | solution 1 for GlobalTheory.T.finite_local_cohomology_at_places_of_localFiniteness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:37.474344+00:00
-- url     : https://prove2.me/submissions/db3e8226-2e0a-45d9-997e-bf3bc5924b52

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDual
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDualStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Galois_PlacesOfS_localFinite_at_places


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, Finite (H0 (ρ.comp (locFam S Av v))) ∧ Finite (H1 (ρ.comp (locFam S Av v))) ∧ Finite (H2 (ρ.comp (locFam S Av v))) := by
  first | exact @GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places | exact GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places | (intros; apply GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places <;> assumption)
end _root_.GlobalTheory.T
