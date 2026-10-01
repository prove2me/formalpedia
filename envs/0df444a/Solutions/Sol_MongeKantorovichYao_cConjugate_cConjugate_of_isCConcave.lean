-- Prove2me | solution 1 for MongeKantorovichYao.cConjugate_cConjugate_of_isCConcave
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:12:54.476184+00:00
-- url     : https://prove2.me/submissions/1a41a100-c14f-4432-baba-030ecaf5a854

import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory MongeKantorovichYao

theorem solution {X Y : Type*}
    (c : X × Y → ℝ) (ψ : X → ℝ) (hψ : IsCConcave c ψ) :
    cConjugate' c (cConjugate c (fun x => (ψ x : EReal))) = fun x => (ψ x : EReal) := by
  obtain ⟨φ, hφ⟩ := hψ
  funext x
  simp only [cConjugate', cConjugate] at hφ ⊢
  apply le_antisymm
  · rw [hφ x]
    apply le_iInf
    intro y
    refine (iInf_le _ y).trans (EReal.sub_le_sub le_rfl ?_)
    apply le_iInf
    intro z
    have hz : (ψ z : EReal) ≤ (c (z, y) : EReal) - (φ y : EReal) :=
      (hφ z).trans_le (iInf_le _ y)
    norm_cast at hz ⊢
    linarith
  · apply le_iInf
    intro y
    calc
      (ψ x : EReal) = (c (x, y) : EReal) - ((c (x, y) : EReal) - (ψ x : EReal)) := by
        norm_cast
        ring
      _ ≤ (c (x, y) : EReal) - ⨅ z, (c (z, y) : EReal) - (ψ z : EReal) :=
        EReal.sub_le_sub le_rfl (iInf_le _ x)
