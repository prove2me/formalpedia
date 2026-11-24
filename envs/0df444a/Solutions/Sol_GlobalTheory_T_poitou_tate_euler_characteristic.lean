-- Prove2me | solution 1 for GlobalTheory.T.poitou_tate_euler_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:17.7948+00:00
-- url     : https://prove2.me/submissions/273308a6-32d1-46d9-b14c-e6f9887f0269

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateEulerCharacteristic
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateEulerCharacteristicStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_GaloisCoh_selmer_sha_eq_comap_ker


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
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), (∀ L : LocCond ρ (locFam S Av), Sel ρ (locFam S Av) (continuous_locFam S Av) L = (Submodule.pi Set.univ L).comap (loc1 S Av ρ)) ∧ Sha1 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc1 S Av ρ) ∧ Sha2 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc2 S Av ρ) := by
  first | exact @GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker | exact GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker | (intros; apply GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker <;> assumption)
end _root_.GlobalTheory.T
