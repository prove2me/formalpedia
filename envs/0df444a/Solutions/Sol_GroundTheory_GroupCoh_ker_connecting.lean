-- Prove2me | solution 1 for GroundTheory.GroupCoh.ker_connecting
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:58.154482+00:00
-- url     : https://prove2.me/submissions/8562b8fd-2247-4bdf-886f-d135b1cc17fd

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_mk_eq_mk_iff
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
    (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).ker = (KerModRange.map p hfp hgp).range := by
  ext y
  constructor
  · intro hy
    obtain ⟨s, rfl⟩ := connLeft_surjective hp hex hfp y
    rw [AddMonoidHom.mem_ker, connecting_connLeft, connRight_apply,
      KerModRange.mk_eq_zero_iff] at hy
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.1 hy
    have hk : (s : B) - i a ∈ fB.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, ← hfi, ha, apply_connInv, sub_self]
    refine ⟨QuotientAddGroup.mk ⟨_, hk⟩, ?_⟩
    rw [KerModRange.map_mk, connLeft_apply, KerModRange.mk_eq_mk_iff, kerMap_apply]
    have hpa : p (i a) = 0 := (hex _).2 ⟨a, rfl⟩
    rw [map_sub, hpa, sub_zero, sub_self]
    exact zero_mem _
  · rintro ⟨x, rfl⟩
    induction x using QuotientAddGroup.induction_on with
    | H z =>
    obtain ⟨b, hb⟩ := z
    have hb' : b ∈ connDomain fB i := by
      refine AddSubgroup.mem_comap.2 ?_
      rw [AddMonoidHom.mem_ker.1 hb]
      exact zero_mem _
    have h1 : KerModRange.map p hfp hgp (QuotientAddGroup.mk ⟨b, hb⟩ : KerModRange fB gB) =
        connLeft hex hfp ⟨b, hb'⟩ := rfl
    have h2 : connInv hi ⟨b, hb'⟩ = 0 :=
      hi (by rw [apply_connInv, map_zero]; exact AddMonoidHom.mem_ker.1 hb)
    rw [AddMonoidHom.mem_ker, h1, connecting_connLeft, connRight_apply,
      KerModRange.mk_eq_zero_iff]
    simp only [h2]
    exact zero_mem _
end GroundTheory.GroupCoh
