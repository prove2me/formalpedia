-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTate.continuous_cycMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:13.098207+00:00
-- url     : https://prove2.me/submissions/e9d691be-8f07-465a-a90e-441aeebf0a44

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Theorems.Thm_GlobalTheory_Published_PoitouTate_continuous_toZModPow
import Theorems.Thm_ReciprocityTheory_Gal_continuous_cycZ


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
omit [IsAlgClosure F Ω]
namespace GlobalTheory.Published.PoitouTate
theorem _root_.solution [Algebra.IsAlgebraic F Ω] : Continuous (cycMod F Ω l r) := by
  rw [cycMod, MonoidHom.coe_comp]
  exact (Continuous.units_map _ continuous_toZModPow).comp (continuous_cycZ F Ω l)
end GlobalTheory.Published.PoitouTate
