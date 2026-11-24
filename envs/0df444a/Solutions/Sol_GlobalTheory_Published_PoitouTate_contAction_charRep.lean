-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTate.contAction_charRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:14:09.034845+00:00
-- url     : https://prove2.me/submissions/6ad162e1-3c29-441d-a8fd-a87e777df95c

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Theorems.Thm_GlobalTheory_Published_PoitouTate_continuous_cycMod

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
theorem _root_.solution (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) :
    ContAction (charRep μ) := by
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic

  have hc : Continuous μ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have hpull : (μ ∘ (QuotientGroup.mk : G F Ω → GS Ω (S : Set (HeightOneSpectrum (𝓞 F))))) =
        cycMod F Ω l r := by
      rw [← hμ]
      rfl
    rw [hpull]
    exact continuous_cycMod
  show Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × ZMod (l ^ r) =>
    charRep μ p.1 p.2
  simp only [charRep_apply]
  exact (Units.continuous_val.comp (hc.comp continuous_fst)).mul continuous_snd
end GlobalTheory.Published.PoitouTate
