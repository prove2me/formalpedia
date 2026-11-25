-- Prove2me | solution 1 for GlobalTheory.CohTransport.dualityClauses_of_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:48.366912+00:00
-- url     : https://prove2.me/submissions/a179a0e5-de6b-4c8e-a9bc-032993fa75da

import Mathlib
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DualityClausesOfMulEquiv
import Theorems.Thm_GlobalTheory_CohTransport_bijective_of_conj
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
noncomputable section
open GlobalTheory GlobalTheory.CohTransport
namespace GlobalTheory.CohTransport
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (h : ContAction ρ) (h' : ContAction (ρ.comp e.toMonoidHom)), (Nonempty (H2 (charRep (χ.comp e.toMonoidHom)) ≃ₗ[R] R) ∧ Function.Bijective (cupH0H2TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)) ∧ Function.Bijective (cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _) (h'.comp' continuous_id)) ∧ Function.Bijective (cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _) (h'.comp' continuous_id)).flip ∧ Function.Bijective (cup20 (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _))) → (Nonempty (H2 (charRep χ) ≃ₗ[R] R) ∧ Function.Bijective (cupH0H2TwistedDual χ ρ (MonoidHom.id _)) ∧ Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id)) ∧ Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id)).flip ∧ Function.Bijective (cup20 χ ρ (MonoidHom.id _))) := by
  intro R _ _ _ Γ Γ' _ _ _ _ M _ _ _ _ _ e he he' χ ρ h h' H
  have hA : ∀ g m, ((ρ.comp e.toMonoidHom).comp (MonoidHom.id Γ')) g m =
      (ρ.comp (MonoidHom.id Γ)) (e g) m := fun _ _ => rfl
  have hB : ∀ g φ, ((twDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)).comp
      (MonoidHom.id Γ')) g φ = ((twDual χ ρ).comp (MonoidHom.id Γ)) (e g) φ := by
    intro g φ
    refine TDual.ext fun m => ?_
    simp [twDual_apply, map_inv]
  have hC : ∀ g x, ((charRep (χ.comp e.toMonoidHom)).comp (MonoidHom.id Γ')) g x =
      ((charRep χ).comp (MonoidHom.id Γ)) (e g) x := fun _ _ => rfl
  let E0A := eq0 _ _ e hA
  let E0B := eq0 _ _ e hB
  let FrameLocalData := eq1 _ _ e he he' hA
  let E1B := eq1 _ _ e he he' hB
  let E2A := eq2 _ _ e he he' hA
  let E2B := eq2 _ _ e he he' hB
  let E2C := eq2 _ _ e he he' hC
  have c02 : ∀ m y, cupH0H2TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (E0A m) (E2B y) = E2C (cupH0H2TwistedDual χ ρ (MonoidHom.id _) m y) := by
    intro m y
    induction y using Submodule.Quotient.induction_on with
    | H f => rfl
  have c11 : ∀ y x, cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (h'.comp' continuous_id) (E1B y) (FrameLocalData x) =
      E2C (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id) y x) := by
    intro y x
    induction y using Submodule.Quotient.induction_on with
    | H f =>
      induction x using Submodule.Quotient.induction_on with
      | H f' => rfl
  have c20 : ∀ x m, cup20 (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (E2A x) (E0B m) = E2C (cup20 χ ρ (MonoidHom.id _) x m) := by
    intro x m
    induction x using Submodule.Quotient.induction_on with
    | H f => rfl
  obtain ⟨⟨j⟩, b02, b11, b11', b20⟩ := H
  refine ⟨⟨(eq2 (charRep χ) (charRep (χ.comp e.toMonoidHom)) e he he' (fun _ _ => rfl)).trans j⟩,
    bijective_of_conj _ _ E0A E2B E2C c02 b02, bijective_of_conj _ _ E1B FrameLocalData E2C c11 b11,
    bijective_of_conj _ _ FrameLocalData E1B E2C (fun x y => by simp only [LinearMap.flip_apply]; exact c11 y x) b11',
    bijective_of_conj _ _ E2A E0B E2C c20 b20⟩
end GlobalTheory.CohTransport
