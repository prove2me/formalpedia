-- Prove2me | solution 1 for Nock.Verb.Rel_den
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:19.158805+00:00
-- url     : https://prove2.me/submissions/b30d6348-de12-4730-a9ce-db4454c3ccf2

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_Den_null
public import Theorems.Thm_Nock_Verb_Den_star
public import Theorems.Thm_Nock_Verb_Den_slot
public import Theorems.Thm_Nock_Verb_Den_equal
public import Theorems.Thm_Nock_Verb_Den_minus
public import Theorems.Thm_Nock_Verb_Den_edit_node
public import Theorems.Thm_Nock_Verb_Den_edit_leaf
public import Theorems.Thm_Nock_Verb_Den_wut

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution : ∀ (n : Nat) (v w : Verb), v.noun.size ≤ n → Rel v w → editOk v = true →
    ∀ x, (Den v x ↔ Den w x) := by
  intro n
  induction n with
  | zero => intro v w hn _ _ x; cases v <;> simp [Noun.size, Verb.noun] at hn
  | succ n ih =>
      intro v w hn hrel hok x
      cases hrel with
      | leaf => exact Iff.rfl
      | base _ hd => exact hd x
      | @cong a l l' r r' hl hr =>
          simp only [Verb.noun, Noun.size] at hn
          simp only [editOk, Bool.and_eq_true] at hok
          obtain ⟨⟨hcond, hokl⟩, hokr⟩ := hok
          have El : ∀ y, Den l y ↔ Den l' y := fun y => ih l l' (by omega) hl hokl y
          have Er : ∀ y, Den r y ↔ Den r' y := fun y => ih r r' (by omega) hr hokr y
          cases a with
          | null =>
              rw [Den_null, Den_null]
              exact ⟨fun ⟨p,q,he,hp,hq⟩ => ⟨p,q,he,(El p).1 hp,(Er q).1 hq⟩,
                     fun ⟨p,q,he,hp,hq⟩ => ⟨p,q,he,(El p).2 hp,(Er q).2 hq⟩⟩
          | star =>
              rw [Den_star, Den_star]
              exact ⟨fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).1 hp,(Er q).1 hq,he⟩,
                     fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).2 hp,(Er q).2 hq,he⟩⟩
          | slot =>
              rw [Den_slot, Den_slot]
              exact ⟨fun ⟨ax,b,hp,hq,hs⟩ => ⟨ax,b,(El _).1 hp,(Er _).1 hq,hs⟩,
                     fun ⟨ax,b,hp,hq,hs⟩ => ⟨ax,b,(El _).2 hp,(Er _).2 hq,hs⟩⟩
          | equal =>
              rw [Den_equal, Den_equal]
              exact ⟨fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).1 hp,(Er q).1 hq,he⟩,
                     fun ⟨p,q,hp,hq,he⟩ => ⟨p,q,(El p).2 hp,(Er q).2 hq,he⟩⟩
          | minus =>
              rw [Den_minus, Den_minus]
              exact ⟨fun ⟨b,hq,hor⟩ => ⟨b,(Er _).1 hq,
                        hor.imp (fun ⟨h,e⟩ => ⟨(El _).1 h,e⟩) (fun ⟨h,e⟩ => ⟨(El _).1 h,e⟩)⟩,
                     fun ⟨b,hq,hor⟩ => ⟨b,(Er _).2 hq,
                        hor.imp (fun ⟨h,e⟩ => ⟨(El _).2 h,e⟩) (fun ⟨h,e⟩ => ⟨(El _).2 h,e⟩)⟩⟩
          | wut =>
              exact ⟨fun h => (Den_wut h).elim, fun h => (Den_wut h).elim⟩
          | edit =>
              cases hr with
              | leaf => exact ⟨fun h => (Den_edit_leaf h).elim, fun h => (Den_edit_leaf h).elim⟩
              | base hp _ =>
                  rw [hp] at hcond; simp at hcond
              | @cong b nw nw' od od' hnw hod =>
                  simp only [Verb.noun, Noun.size] at hn
                  simp only [editOk, Bool.and_eq_true] at hokr
                  obtain ⟨⟨_, hoknw⟩, hokod⟩ := hokr
                  have Enw : ∀ y, Den nw y ↔ Den nw' y := fun y => ih nw nw' (by omega) hnw hoknw y
                  have Eod : ∀ y, Den od y ↔ Den od' y := fun y => ih od od' (by omega) hod hokod y
                  rw [Den_edit_node, Den_edit_node]
                  exact ⟨fun ⟨ax,nn,oo,ha,hn2,ho,he⟩ =>
                          ⟨ax,nn,oo,(El _).1 ha,(Enw _).1 hn2,(Eod _).1 ho,he⟩,
                         fun ⟨ax,nn,oo,ha,hn2,ho,he⟩ =>
                          ⟨ax,nn,oo,(El _).2 ha,(Enw _).2 hn2,(Eod _).2 ho,he⟩⟩
end Nock.Verb
