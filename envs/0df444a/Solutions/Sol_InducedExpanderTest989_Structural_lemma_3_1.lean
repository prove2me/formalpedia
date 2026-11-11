-- Prove2me | solution 1 for InducedExpanderTest989.Structural.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T00:08:45.767223+00:00
-- url     : https://prove2.me/submissions/3b71a531-0c5f-4a2d-b13a-5d3b9a56d819

import Definitions.Def_InducedExpanderTest989_Structural_Graph

set_option autoImplicit false
open InducedExpanderTest989.Structural

theorem solution {n d : ℕ} (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    (hG : DegreeBound d G) (α α' ϕ ϕ' : ℝ)
    (hα : 0 < α ∧ α ≤ 1) (hα' : 0 < α' ∧ α' ≤ 1)
    (hϕ : 0 < ϕ ∧ ϕ ≤ 1) (hϕ' : 0 < ϕ' ∧ ϕ' ≤ 1)
    (ha : α' ≤ α) (hf : ϕ' ≤ ϕ) : HasCore d G α ϕ → HasCore d G α' ϕ'  := by
  intro h
  obtain ⟨U, hsize, hconductance⟩ := h
  exact ⟨U,
    le_trans (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n)) hsize,
    le_trans hf hconductance⟩

