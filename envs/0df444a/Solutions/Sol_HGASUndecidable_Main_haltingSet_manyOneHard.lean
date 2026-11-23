-- Prove2me | solution 1 for HGASUndecidable.Main.haltingSet_manyOneHard
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:41:38.277741+00:00
-- url     : https://prove2.me/submissions/73cc44f1-0def-41cd-a289-ea15952e40b3

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators
open HGASUndecidable.Main

theorem solution : ManyOneHard haltingSet := by
  intro A hA
  let f : ℕ →. ℕ := fun a =>
    (Part.assert (A a) (fun _ => Part.some ())).map (fun _ => 0)
  have hp : Partrec f := hA.map ((Computable.const 0).comp Computable.snd)
  have hp' : Nat.Partrec f := Partrec.nat_iff.mp hp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp'
  refine ⟨fun a => Nat.pair (Encodable.encode c) a, ?_, ?_⟩
  · exact Computable.pair (Computable.const _) Computable.id
  · intro a
    simp only [haltingSet]
    rw [← Nat.Partrec.Code.ofNatCode_eq]
    simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
    rw [hc]
    simp only [f]
    exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
