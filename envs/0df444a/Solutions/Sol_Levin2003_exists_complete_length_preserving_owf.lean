-- Prove2me | solution 1 for Levin2003.exists_complete_length_preserving_owf
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:45:44.159784+00:00
-- url     : https://prove2.me/submissions/f13a4ed6-ae4c-491a-873a-98fc4253b65a

import Definitions.Def_Levin2003_tiling_expansion
open Levin2003

theorem solution :
    ∃ U : Bits → Bits, PolyTimeComputable U ∧ LengthPreserving U ∧
      (OneWay U ↔ ∃ f : Bits → Bits, OneWay f) := by
  by_cases h : ∃ f : Bits → Bits, OneWay f
  · obtain ⟨f, hf⟩ := h
    exact ⟨f, hf.1, hf.2.1, ⟨fun _ => ⟨f, hf⟩, fun _ => hf⟩⟩
  · refine ⟨id, ⟨Turing.idComputableInPolyTime (id : Bits → List Bool)⟩, fun w => rfl,
      ⟨fun hU => ⟨id, hU⟩, fun hex => (h hex).elim⟩⟩
