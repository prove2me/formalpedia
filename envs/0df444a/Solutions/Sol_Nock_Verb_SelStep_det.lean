-- Prove2me | solution 1 for Nock.Verb.SelStep.det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:20.42325+00:00
-- url     : https://prove2.me/submissions/1a1887df-e53b-4f27-b558-89ab9ea44ee2

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
namespace SelStep
theorem _root_.solution {lt : Nat → Nat → Prop} (hs : StrictSelect lt) {a b b' : Verb}
    (h : SelStep lt a b) (h' : SelStep lt a b') : b = b' := by
  obtain ⟨i, sub, r, ⟨hip, hmax⟩, hmap, _, hred, hb⟩ := h
  obtain ⟨i', sub', r', ⟨hip', hmax'⟩, hmap', _, hred', hb'⟩ := h'
  have hii : i = i' := by
    rcases Classical.em (i = i') with heq | hne
    · exact heq
    · rcases hs.total hne with hlt | hlt
      · exact absurd hlt (hmax i' hip')
      · exact absurd hlt (hmax' i hip)
  subst hii
  have hsub : sub = sub' := Option.some.inj (hmap.symm.trans hmap')
  subst hsub
  have hr : r = r' := Option.some.inj (hred.symm.trans hred')
  subst hr
  exact hb.trans hb'.symm
end SelStep
end Nock.Verb
