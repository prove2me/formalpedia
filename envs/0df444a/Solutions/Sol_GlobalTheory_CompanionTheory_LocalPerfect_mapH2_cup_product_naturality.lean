-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalPerfect.mapH2_cup_product_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:39.696527+00:00
-- url     : https://prove2.me/submissions/828dc46f-6ef0-40f5-82b1-0a54ec672dbb

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
theorem _root_.solution (h : χ.comp φ = χ') (hc : ContAction (ρ.comp φ))
    (hc' : ContAction ((ρ.comp φ).comp (MonoidHom.id D)))
    (hq : ∀ (g : D) (m : R), ((charRep χ).comp φ) g m = charRep χ' g m)
    (y : H1 ((twDual χ ρ).comp φ)) (x : H1 (ρ.comp φ)) :
    mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y x) =
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y) (coefMap ρ φ x) := by
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
end GlobalTheory.CompanionTheory.LocalPerfect
