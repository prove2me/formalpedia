-- Prove2me | solution 1 for MITMSynthesis.star_mem_depthOneSet
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-10T12:29:34.045731+00:00
-- url     : https://prove2.me/submissions/83bd98a5-ba50-48d6-8a5a-e3a3ec44c8ce

import Mathlib.Data.List.Pairwise
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S

open MITMSynthesis

private def inversePlacement {n : ℕ} (p : Placement n) : Placement n :=
  ⟨p.gate.inv, p.qubits⟩

private theorem inverse_placement_unitary {n : ℕ} (p : Placement n) :
    (inversePlacement p).unitary = star p.unitary := by
  classical
  ext x y
  have hSwap : (∀ j, j ∉ Set.range p.qubits → x j = y j) ↔
      (∀ j, j ∉ Set.range p.qubits → y j = x j) :=
    ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩
  change (if (∀ j, j ∉ Set.range p.qubits → x j = y j) then
    star ((p.gate.mat : Matrix (Q p.gate.arity) (Q p.gate.arity) ℂ) (y ∘ p.qubits) (x ∘ p.qubits))
      else 0) = star (if (∀ j, j ∉ Set.range p.qubits → y j = x j) then
    (p.gate.mat : Matrix (Q p.gate.arity) (Q p.gate.arity) ℂ) (y ∘ p.qubits) (x ∘ p.qubits) else 0)
  by_cases h : ∀ j, j ∉ Set.range p.qubits → x j = y j
  · simp only [if_pos h, if_pos (hSwap.mp h)]
  · have h' : ¬(∀ j, j ∉ Set.range p.qubits → y j = x j) := fun hy => h (hSwap.mpr hy)
    simp only [if_neg h, if_neg h', star_zero]

private theorem inverse_layer_unitary {n : ℕ} (L : List (Placement n)) :
    layerUnitary (L.reverse.map inversePlacement) = star (layerUnitary L) := by
  induction L with
  | nil => simp [layerUnitary]
  | cons p L ih =>
    simp only [List.reverse_cons, layerUnitary, List.map_append, List.map_nil,
      List.prod_append, List.prod_nil, List.map_cons, List.prod_cons, mul_one, star_mul,
      inverse_placement_unitary] at ih ⊢
    rw [ih]

theorem solution {n : ℕ} {G : Set Gate} (hG : IsInstructionSet G)
    {M : Matrix (Q n) (Q n) ℂ} (hM : M ∈ depthOneSet n G) : star M ∈ depthOneSet n G := by
  obtain ⟨L, ⟨hnonempty, hgates, hdisjoint⟩, rfl⟩ := hM
  refine ⟨L.reverse.map inversePlacement, ⟨?_, ?_, ?_⟩, inverse_layer_unitary L⟩
  · simpa using hnonempty
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hG q.gate (hgates q (List.mem_reverse.mp hq))
  · rw [List.pairwise_map, List.pairwise_reverse]
    exact hdisjoint.imp (fun hpq => hpq.symm)

#print axioms solution
