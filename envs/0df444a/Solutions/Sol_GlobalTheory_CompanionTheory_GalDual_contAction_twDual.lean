-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GalDual.contAction_twDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:14:09.784824+00:00
-- url     : https://prove2.me/submissions/38597622-318f-4469-b341-2b698e0a56d7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SelmerGroupDualExact
import Theorems.Thm_GlobalTheory_CompanionTheory_GalDual_contAction_twDual_of_continuous
import Theorems.Thm_GlobalTheory_Published_PoitouTate_continuous_cycMod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GalDual
namespace GlobalTheory.CompanionTheory.GalDual
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ), μ.comp (toGS Ω _) = cycMod F Ω l r → ContAction (twDual μ ρ) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ hμ
  have hc : Continuous μ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (μ ∘ QuotientGroup.mk : G F Ω → _) = cycMod F Ω l r := by rw [← hμ]; rfl
    rw [this]; exact continuous_cycMod
  exact contAction_twDual_of_continuous μ hc ρ hρ
end GlobalTheory.CompanionTheory.GalDual
