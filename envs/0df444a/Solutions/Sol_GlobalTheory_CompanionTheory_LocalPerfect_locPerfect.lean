-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalPerfect.locPerfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:29:53.392422+00:00
-- url     : https://prove2.me/submissions/f8592ed2-0d19-4ae4-a397-95161c808ae8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalizationExact
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_LocalPerfect_injective_compr__4c0b8fced67e
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
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalPerfect
namespace GlobalTheory.CompanionTheory.LocalPerfect
theorem _root_.solution (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ) (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (hT : LocalTateDuality)
    (hr : 0 < r) (inv : InvFam F Ω l r)
    (hinv : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A))
    (hA : ∀ v : S, IsPlaceOver (Av v) v.1) (v : S) :
    Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v)
        (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)) ∧
      Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v)
        (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)).flip := by
  have hc := hρ.comp' (continuous_locFam S Av v)
  have hχ : μ.comp (locFam S Av v) = (cycMod F Ω l r).comp (Dec (F := F) (Av v)).subtype :=
    MonoidHom.ext fun g => DFunLike.congr_fun hμ (g : G F Ω)
  obtain ⟨-, -, h1, h2, -⟩ := hT F Ω l r M (Av v) (ρ.comp (locFam S Av v)) v.1 hr (hA v) hc
  exact injective_compr₂ μ ρ (locFam S Av v) _ hχ _ (hc.comp' continuous_id)
    (locFam_apply_eq S Av μ hμ v) (hinv _ _ (hA v)).1 h1.1 h2.1
end GlobalTheory.CompanionTheory.LocalPerfect
