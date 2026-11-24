-- Prove2me | solution 1 for GlobalTheory.contCohomology_transport_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:53.300698+00:00
-- url     : https://prove2.me/submissions/23820b35-fdfa-4554-a442-0e90101c53be

import Mathlib
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ContCohomologyTransportMulEquiv
import Theorems.Thm_GlobalTheory_dn_comp_monoidHom
import Theorems.Thm_GlobalTheory_Published_subsingleton_Hn_succ_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (ρ : Representation R Γ M) (ρ' : Representation R Γ' M), (∀ g m, ρ' g m = ρ (e g) m) → Nonempty (H1 ρ ≃ H1 ρ') ∧ Nonempty (H2 ρ ≃ H2 ρ') ∧ (Subsingleton (Hn ρ 3) → Subsingleton (Hn ρ' 3)) := by
  intro R _ Γ Γ' _ _ _ _ M _ _ _ _ e he he' ρ ρ' h
  have h' : ∀ g m, ρ g m = ρ' (e.symm g) m := fun g m => by rw [h, e.apply_symm_apply]
  refine ⟨⟨⟨pairH1DecompositionMap ρ ρ' e.toMonoidHom he LinearMap.id continuous_id (fun g m => (h g m).symm),
      pairH1DecompositionMap ρ' ρ e.symm.toMonoidHom he' LinearMap.id continuous_id (fun g m => (h' g m).symm),
      ?_, ?_⟩⟩,
    ⟨⟨compatiblePairH2 ρ ρ' e.toMonoidHom he LinearMap.id continuous_id (fun g m => (h g m).symm),
      compatiblePairH2 ρ' ρ e.symm.toMonoidHom he' LinearMap.id continuous_id (fun g m => (h' g m).symm),
      ?_, ?_⟩⟩, ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (e.apply_symm_apply g)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (e.symm_apply_apply g)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (Prod.ext (e.apply_symm_apply g.1) (e.apply_symm_apply g.2))
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (Prod.ext (e.symm_apply_apply g.1) (e.symm_apply_apply g.2))
  · intro hs
    rw [GlobalTheory.Published.subsingleton_Hn_succ_iff] at hs ⊢
    intro f hf hd
    obtain ⟨c, hc, hcf⟩ := hs (fun x => f (fun i => e.symm (x i)))
      (hf.comp (continuous_pi fun i => he'.comp (continuous_apply i))) (by
        funext g
        have := dn_comp_monoidHom e.symm.toMonoidHom ρ' ρ h' 3 f g
        rw [hd] at this
        exact this)
    refine ⟨fun x => c (fun i => e (x i)),
      hc.comp (continuous_pi fun i => he.comp (continuous_apply i)), ?_⟩
    funext g
    have := dn_comp_monoidHom e.toMonoidHom ρ ρ' h 2 c g
    rw [hcf] at this
    refine this.trans ?_
    exact congrArg f (funext fun i => e.symm_apply_apply _)
end GlobalTheory
