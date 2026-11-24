-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalPerfect.coefMap_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:37.612098+00:00
-- url     : https://prove2.me/submissions/d6b645b2-1518-4a11-be22-07f55af3c466

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalizationExact

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
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]
  {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ) (χ' : D →* Rˣ)
namespace GlobalTheory.CompanionTheory.LocalPerfect
theorem _root_.solution : Function.Bijective (coefMap ρ φ) := by
  refine Function.bijective_iff_has_inverse.2 ⟨mapH1 ((ρ.comp φ).comp (MonoidHom.id D)) (ρ.comp φ)
    LinearMap.id continuous_id (fun _ _ => rfl), fun x => ?_, fun x => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl
end GlobalTheory.CompanionTheory.LocalPerfect
