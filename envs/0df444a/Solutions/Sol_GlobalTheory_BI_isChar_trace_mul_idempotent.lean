-- Prove2me | solution 1 for GlobalTheory.BI.isChar_trace_mul_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:13.111052+00:00
-- url     : https://prove2.me/submissions/704a5e87-8efb-4a79-96c3-d811b8eeca97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharTraceMulIdempotent
import Theorems.Thm_GlobalTheory_BI_isChar_and_isIrrChar_of_rep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
namespace _root_.GlobalTheory.BI
theorem _root_.solution :
    ∀ (L : Type) [Field L] (T : Type) [Group T] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L T V) (e : Module.End L V), e * e = e → (∀ t, ρ t * e = e * ρ t) → _root_.GlobalTheory.BI.IsChar L L (fun t => LinearMap.trace L V (ρ t * e)) := by
  intro L _ T _ V _ _ _ ρ e he hc
  have hfix : ∀ v ∈ LinearMap.range e, e v = v := by
    rintro _ ⟨w, rfl⟩
    rw [← Module.End.mul_apply, he]
  let W : Subrepresentation ρ :=
    ⟨LinearMap.range e, fun t v hv => by
      obtain ⟨w, rfl⟩ := hv
      exact ⟨ρ t w, by rw [← Module.End.mul_apply e, ← hc t, Module.End.mul_apply]⟩⟩
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep L L T _ W.toRepresentation).1
  convert key using 2 with t
  rw [Algebra.algebraMap_self, RingHom.id_apply, Representation.character,
    ← LinearMap.trace_restrict_eq_of_forall_mem (LinearMap.range e) (ρ t * e)
      (fun x => ⟨ρ t x, by rw [hc t]; rfl⟩)]
  congr 1
  ext ⟨v, hv⟩
  change (ρ t * e) v = ρ t v
  rw [Module.End.mul_apply, hfix v hv]
end _root_.GlobalTheory.BI
end GlobalTheory.BI
