-- Prove2me | solution 1 for HuangYin.case_vL_vL_optimal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T13:43:24.299062+00:00
-- url     : https://prove2.me/submissions/cd8ae7da-b78b-4ac8-b490-20f0a10457c3

import Mathlib
import Definitions.Def_HuangYin_OptimalOffer

open HuangYin in
theorem solution (P : Params) : HuangYin.OptimalOffer P P.vL P.vL 0 0 := by
  have hb : ∀ b : Bool, HuangYin.Buys P P.vL b := by
    intro b
    unfold HuangYin.Buys HuangYin.estimate
    have hv := P.hv
    cases b <;> norm_num <;> nlinarith
  have hd : ∀ q, HuangYin.demand P P.vL q = 1 := by
    intro q
    unfold HuangYin.demand
    rw [if_pos (hb false), if_pos (hb true)]
    ring
  refine ⟨⟨le_refl 0, zero_le_one⟩, ⟨le_refl 0, zero_le_one⟩, ?_⟩
  intro y1 hy1 y2 hy2
  unfold HuangYin.opaqueProfit
  rw [hd, hd, hd, hd]
  unfold HuangYin.cost
  have hc := P.hc
  nlinarith [hy1.1, hy2.1]
