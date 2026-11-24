-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Duality.pi_perpCond_eq_annihilator_sumPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:12.570826+00:00
-- url     : https://prove2.me/submissions/eacdcbbe-25eb-40e7-bb1e-f893aa8cdc5e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PiPerpCondEqAnnihilatorSumPair
import Theorems.Thm_GlobalTheory_Published_PoitouTate_NineTermExact_sum_eq_zero
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Duality
namespace GlobalTheory.CompanionTheory.Duality
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ v, Function.Injective (j v)) → ∀ L : LocCond ρ (locFam S Av), Submodule.pi Set.univ (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) L) = ⨅ x ∈ Submodule.pi Set.univ L, LinearMap.ker ((sumPair S Av μ j ρ hρ).flip x) := by
  classical
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ j hj L
  ext y
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, forall_const, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.flip_apply, ReciprocityTheory.Gal.perpCond, PositivityTheory.S2pt.sumPair, Finset.sum_apply,
    LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearMap.proj_apply]
  constructor
  · intro h x hx
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [h v (x v) (hx v), map_zero]
  · intro h v x0 hx0
    apply hj v
    rw [map_zero]
    have hs := h (Pi.single v x0) (fun w => by
      by_cases hw : w = v
      · subst hw
        simpa using hx0
      · simp [Pi.single_eq_of_ne hw])
    rw [Finset.sum_eq_single v] at hs
    · simpa using hs
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw]
    · simp
end GlobalTheory.CompanionTheory.Duality
