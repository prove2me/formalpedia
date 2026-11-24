-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GalDual.contAction_twDual_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:31.584816+00:00
-- url     : https://prove2.me/submissions/b9606e4e-9f1d-45d7-b937-df029e92e121

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SelmerGroupDualExact

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
theorem _root_.solution {R Γ M : Type*} [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [AddCommGroup M]
    [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (χ : Γ →* Rˣ)
    (hχ : Continuous χ) (ρ : Representation R Γ M) (hρ : ContAction ρ) :
    ContAction (twDual χ ρ) := by
  have key : ∀ φ : TDual R M, Continuous (fun g : Γ => twDual χ ρ g φ) := by
    intro φ
    rw [continuous_discrete_rng]
    intro ψ
    have hset : (fun g : Γ => twDual χ ρ g φ) ⁻¹' {ψ} =
        ⋂ m : M, (fun g : Γ => ((χ g : Rˣ) : R) * φ (ρ g⁻¹ m)) ⁻¹' {ψ m} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      exact ⟨fun h m => by rw [← h]; rfl, fun h => TDual.ext h⟩
    rw [hset]
    refine isOpen_iInter_of_finite fun m => ?_
    have h1 : Continuous fun g : Γ => ρ g⁻¹ m :=
      Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) hρ
        (continuous_inv.prodMk continuous_const)
    have h2 : Continuous fun g : Γ => φ (ρ g⁻¹ m) :=
      (continuous_of_discreteTopology (f := fun x : M => φ x)).comp h1
    have h3 : Continuous fun g : Γ => ((χ g : Rˣ) : R) * φ (ρ g⁻¹ m) :=
      (Units.continuous_val.comp hχ).mul h2
    exact (isOpen_discrete {ψ m}).preimage h3
  exact continuous_prod_of_discrete_right.2 key
end GlobalTheory.CompanionTheory.GalDual
