-- Prove2me | solution 1 for GlobalTheory.T.artin_transport_algClosure_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:40:08.527261+00:00
-- url     : https://prove2.me/submissions/a0d627e3-e511-45b7-b57a-d7fbb774c100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ArtinTransportAlgClosureEquiv
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ArtinTransportAlgClosureEquivStatement
import Theorems.Thm_GlobalTheory_ArtinTransport_chi_artin_transport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] [Algebra E E'] (φ : Ω ≃+* Ω'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x)) → ∀ (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (art' : Neutral.B1.Ideles E' →* GlobalTheory.HeckeGal.Gab E' Ω'), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → ∀ (ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω), (∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ) → ∀ (B : Type) [CommGroup B] (χ : GlobalTheory.HeckeGal.Gab E Ω →* B) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')), w.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = v.asIdeal → (∀ x, Formalism.L2.Host.IsUnitAt v x → χ (art (Neutral.B1.localIdele E v x)) = 1) → (∀ x, Formalism.L2.Host.IsUnitAt w x → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = 1) ∧ ∀ x ϖ, Formalism.L2.Host.IsUnifAt w x → Formalism.L2.Host.IsUnifAt v ϖ → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = χ (art (Neutral.B1.localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers E) := by
  first | exact @GlobalTheory.ArtinTransport.chi_artin_transport | exact GlobalTheory.ArtinTransport.chi_artin_transport | (intros; apply GlobalTheory.ArtinTransport.chi_artin_transport <;> assumption)
end _root_.GlobalTheory.T
