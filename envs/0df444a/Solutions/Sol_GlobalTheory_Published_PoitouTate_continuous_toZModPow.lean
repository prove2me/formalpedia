-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTate.continuous_toZModPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:01.207801+00:00
-- url     : https://prove2.me/submissions/3eddf519-3abf-49a9-8339-f262c352bf56

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
variable {S Av μ j ρ}
namespace GlobalTheory.Published.PoitouTate
theorem _root_.solution : Continuous (PadicInt.toZModPow r : ℤ_[l] → ZMod (l ^ r)) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) ?_
  rw [ContinuousAt, map_zero, nhds_discrete (ZMod (l ^ r)), Filter.tendsto_pure, Metric.eventually_nhds_iff]
  refine ⟨(l : ℝ) ^ (-(r : ℤ)), zpow_pos hl0 _, fun y hy => ?_⟩
  rw [dist_zero_right] at hy
  have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow y r).1 hy.le
  rw [← PadicInt.ker_toZModPow] at hmem
  exact (RingHom.mem_ker).1 hmem
end GlobalTheory.Published.PoitouTate
