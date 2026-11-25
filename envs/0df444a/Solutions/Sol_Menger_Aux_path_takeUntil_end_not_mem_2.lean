-- Prove2me | solution 2 for Menger.Aux.path_takeUntil_end_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:48:13.564792+00:00
-- url     : https://prove2.me/submissions/80fd1c2b-9d07-454a-97ee-d83fa725de38

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution [DecidableEq V] {H : SimpleGraph V} {a v w : V}
    (p : H.Walk a v) (hp : p.IsPath) (hw : w ∈ p.support) (hne : w ≠ v) :
    v ∉ (p.takeUntil w hw).support := by
  intro hv
  have hnd := hp.support_nodup
  rw [← p.take_spec hw, Walk.support_append] at hnd
  have h2 : v ∈ (p.dropUntil w hw).support.tail := Walk.end_mem_tail_support_of_ne hne _
  exact List.disjoint_of_nodup_append hnd hv h2
end Menger.Aux
