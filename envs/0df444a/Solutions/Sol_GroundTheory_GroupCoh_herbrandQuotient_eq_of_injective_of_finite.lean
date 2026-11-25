-- Prove2me | solution 1 for GroundTheory.GroupCoh.herbrandQuotient_eq_of_injective_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:46:21.305091+00:00
-- url     : https://prove2.me/submissions/d3d32b97-cba3-43a5-bcb5-a05f5b10972f

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_herbrandQuotient_eq_of_shortExact_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
namespace GroundTheory.GroupCoh
theorem _root_.solution {fA gA : A →+ A} {fB gB : B →+ B}
    {i : A →+ B} (hi : Function.Injective i) [Finite (B ⧸ i.range)]
    (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    herbrandQuotient fA gA = herbrandQuotient fB gB := by
  have hf : i.range ≤ i.range.comap fB := by
    rintro _ ⟨a, rfl⟩
    exact AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ⟨fA a, hfi a⟩)
  have hg : i.range ≤ i.range.comap gB := by
    rintro _ ⟨a, rfl⟩
    exact AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ⟨gA a, hgi a⟩)
  refine herbrandQuotient_eq_of_shortExact_of_finite (p := QuotientAddGroup.mk' i.range)
    (fC := QuotientAddGroup.map _ _ fB hf) (gC := QuotientAddGroup.map _ _ gB hg) hi
    (QuotientAddGroup.mk'_surjective _) ?_ hfi hgi (fun _ => rfl) (fun _ => rfl) hfgB hgfB
  intro b
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range,
    Set.mem_range]
end GroundTheory.GroupCoh
