-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTateTotallyComplex.annihilators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:29:48.161826+00:00
-- url     : https://prove2.me/submissions/56e7e4a4-ff72-440e-b57b-03838130cf40

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Theorems.Thm_GlobalTheory_Published_PoitouTate_NineTermExact_mem_range_localization_H1_iff
import Theorems.Thm_GlobalTheory_Published_PoitouTate_NineTermExact_mem_range_localization_H2_iff
import Theorems.Thm_GlobalTheory_Published_PoitouTate_NineTermExact_sum_eq_zero
import Theorems.Thm_GlobalTheory_Published_PoitouTate_contAction_charRep
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open PoitouTate
namespace GlobalTheory.Published
namespace PoitouTateTotallyComplex
theorem _root_.solution (h : PoitouTateTotallyComplex)
    (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ r)) :
    ∃ inv : InvFam F Ω l r, IsLocalInvariants ζ inv ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
    ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
      (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r),
    (∀ x : H2 (charRep μ), ∑ v : S, invAt S Av μ hμ inv v
      (resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) x) = 0) ∧
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M]
      (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hρ : ContAction ρ),
      (∀ x : ∀ v : S, H1 (ρ.comp (locFam S Av v)),
        x ∈ LinearMap.range (loc1 S Av ρ) ↔ ∀ y : H1 (twDual μ ρ),
          ∑ v : S, invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v)
            (hρ.comp' (continuous_locFam S Av v))
            (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y) (x v)) = 0) ∧
      (∀ x : ∀ v : S, H2 (ρ.comp (locFam S Av v)),
        x ∈ LinearMap.range (loc2 S Av ρ) ↔ ∀ y : H0 (twDual μ ρ),
          ∑ v : S, invAt S Av μ hμ inv v (cup20 μ ρ (locFam S Av v) (x v)
            (resH0 (twDual μ ρ) (locFam S Av v) y)) = 0) ∧
      Finite (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) ∧
      Finite (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) ∧
      Nat.card (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) =
        Nat.card (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨inv, hinv, hall⟩ := h F Ω l r hr ζ hζ
  refine ⟨inv, hinv, fun S hS Av hAv μ hμ => ⟨fun x => ?_, fun M _ _ _ _ _ ρ hρ => ?_⟩⟩
  · have hρμ := contAction_charRep hμ
    exact (hall S hS Av hAv μ hμ (ZMod (l ^ r)) (charRep μ) hρμ).1.sum_eq_zero x
  · obtain ⟨hN, hSha⟩ := hall S hS Av hAv μ hμ M ρ hρ
    exact ⟨fun x => hN.mem_range_localization_H1_iff x, fun x => hN.mem_range_localization_H2_iff x,
      hSha.1.1, hSha.1.2.1, hSha.1.2.2.2⟩
end PoitouTateTotallyComplex
end GlobalTheory.Published
