-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTate.poitouTateNineTerm_transgressionZero_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:27.548108+00:00
-- url     : https://prove2.me/submissions/eca6d4c0-8a90-4ede-b435-a7af156ebab1

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a

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
namespace GlobalTheory.Published.PoitouTate
theorem _root_.solution (x : ∀ v : S, H0 (ρ.comp (locFam S Av v))) (y : H2 (twDual μ ρ)) :
    tr0 S Av μ j ρ x y = ∑ v : S, j v (cupH0H2TwistedDual μ ρ (locFam S Av v) (x v)
      (resH2 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y)) := by
  simp only [tr0, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
    LinearMap.proj_apply]
end GlobalTheory.Published.PoitouTate
