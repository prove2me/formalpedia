-- Prove2me | solution 1 for GroundTheory.GroupCoh.KerModRange.ker_map_eq_range_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:26.574745+00:00
-- url     : https://prove2.me/submissions/d4524086-8947-42a9-8ab5-d5dddd0260f2

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_map_mk

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
namespace KerModRange
theorem _root_.solution (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfp : ∀ b, p (fB b) = fC (p b)) (hgp : ∀ b, p (gB b) = gC (p b))
    (hfgB : ∀ b, fB (gB b) = 0) :
    (KerModRange.map p hfp hgp).ker = (KerModRange.map i hfi hgi).range := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
  obtain ⟨b, hb⟩ := z
  rw [AddMonoidHom.mem_ker, KerModRange.map_mk, KerModRange.mk_eq_zero_iff, kerMap_apply,
    AddMonoidHom.mem_range]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.1 h
    obtain ⟨b', rfl⟩ := hp c
    obtain ⟨a, ha⟩ : b - gB b' ∈ Set.range i :=
      (hex _).1 (by rw [map_sub, hgp, hc, sub_self])
    have hfa : fA a = 0 := hi (by
      rw [hfi, ha, map_sub, hfgB, AddMonoidHom.mem_ker.1 hb, sub_zero, map_zero])
    refine ⟨QuotientAddGroup.mk ⟨a, hfa⟩, ?_⟩
    rw [KerModRange.map_mk, KerModRange.mk_eq_mk_iff, kerMap_apply]
    exact AddMonoidHom.mem_range.2 ⟨-b', by rw [ha, map_neg]; abel⟩
  · rintro ⟨y, hy⟩
    induction y using QuotientAddGroup.induction_on with
    | H w =>
    obtain ⟨a, ha⟩ := w
    rw [KerModRange.map_mk, KerModRange.mk_eq_mk_iff, kerMap_apply] at hy
    obtain ⟨b'', hb''⟩ := AddMonoidHom.mem_range.1 hy
    have hpa : p (i a) = 0 := (hex _).2 ⟨a, rfl⟩
    refine AddMonoidHom.mem_range.2 ⟨-p b'', ?_⟩
    have : b = i a - gB b'' := by rw [hb'']; abel
    show gC (-p b'') = p b
    rw [this, map_sub, hpa, hgp, map_neg, zero_sub]
end KerModRange
end GroundTheory.GroupCoh
