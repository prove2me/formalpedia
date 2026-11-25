-- Prove2me | solution 1 for GlobalTheory.JHMult.jhMult_sub_add_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:07.474097+00:00
-- url     : https://prove2.me/submissions/2032950b-e789-4bae-ba8e-0d6a643d9124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Theorems.Thm_GlobalTheory_JHMult_jhMult_exact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.JHMult
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
namespace GlobalTheory.JHMult
theorem _root_.solution {σ : Representation F G W} {ρ : Representation F G V}
    (hσ : σ.IsIrreducible) (S : Subrepresentation ρ) :
    jhMult σ ρ = jhMult σ S.toRepresentation + jhMult σ (subQuot ⊤ S) := by
  let ι : S.toRepresentation.IntertwiningMap ρ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let p : ρ.IntertwiningMap (subQuot ⊤ S) :=
    ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id
      (fun _ => trivial), fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  refine jhMult_exact ι p hσ Subtype.val_injective (fun x => ?_) (fun u => (hp _).2 u.2)
    fun v hv => ⟨⟨v, (hp v).1 hv⟩, rfl⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨v.1, rfl⟩
end GlobalTheory.JHMult
