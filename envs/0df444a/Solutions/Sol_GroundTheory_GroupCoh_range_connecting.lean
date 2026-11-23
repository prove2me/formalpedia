-- Prove2me | solution 1 for GroundTheory.GroupCoh.range_connecting
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:56.566741+00:00
-- url     : https://prove2.me/submissions/7be2097c-59c1-407d-8f99-4dd8bb676dcc

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_map_mk
import Theorems.Thm_GroundTheory_GroupCoh_connecting_connLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}
namespace GroundTheory.GroupCoh
theorem _root_.solution (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).range = (KerModRange.map i hgi hfi).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨s, rfl⟩ := connLeft_surjective hp hex hfp y
    rw [AddMonoidHom.mem_ker, connecting_connLeft, connRight_apply, KerModRange.map_mk,
      KerModRange.mk_eq_zero_iff, kerMap_apply, apply_connInv]
    exact AddMonoidHom.mem_range.2 ⟨s, rfl⟩
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | H z =>
    obtain ⟨a, ha⟩ := z
    rw [AddMonoidHom.mem_ker, KerModRange.map_mk, KerModRange.mk_eq_zero_iff,
      kerMap_apply] at hx
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 hx
    have hb' : b ∈ connDomain fB i := by
      refine AddSubgroup.mem_comap.2 ?_
      rw [hb]
      exact AddMonoidHom.mem_range.2 ⟨a, rfl⟩
    refine ⟨connLeft hex hfp ⟨b, hb'⟩, ?_⟩
    rw [connecting_connLeft, connRight_apply]
    have : connInv hi ⟨b, hb'⟩ = a := hi (by rw [apply_connInv]; exact hb)
    congr 1
    exact Subtype.ext this
end GroundTheory.GroupCoh
