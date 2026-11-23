-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTate.poitouTateNineTerm_transgressionOne_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:46.454717+00:00
-- url     : https://prove2.me/submissions/1d42a80b-8b03-4c47-8c6d-97ac7777fcb4

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
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
open GlobalTheory.Published.PoitouTate
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
variable (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
namespace GlobalTheory.Published.PoitouTate
theorem _root_.solution (hρ : ContAction ρ) (x : ∀ v : S, H1 (ρ.comp (locFam S Av v)))
    (y : H1 (twDual μ ρ)) :
    tr1 S Av μ j ρ hρ x y = ∑ v : S, j v (cupH1H1TwistedDual μ ρ (locFam S Av v)
      (hρ.comp' (continuous_locFam S Av v))
      (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y) (x v)) := by
  simp only [tr1, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
    LinearMap.flip_apply, LinearMap.proj_apply]
end GlobalTheory.Published.PoitouTate
