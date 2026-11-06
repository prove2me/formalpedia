-- Prove2me | solution 1 for OAI.SevenEighths.InverseInitialMarkedReserve.exists_reserve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:47.829961+00:00
-- url     : https://prove2.me/submissions/4f9cf0a8-0c0c-4eb1-8146-4bc335b11226

import Definitions.Def_OAI_NumberTheory_DirichletL_Endpoint
import Definitions.Def_OAI_NumberTheory_DirichletL_Inversion_InitialMarkedReserve

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseInitialMarkedReserve
namespace OAI.SevenEighths.InverseInitialMarkedReserve
theorem _root_.solution (εm:ℝ)(hε:0<εm):
    ∃ρ gap η τ π eps loss:ℝ,
      0<ρ ∧ ρ≤1/4 ∧ ρ≤εm/4 ∧
      0<gap ∧ 2*gap≤ρ ∧
      0<η ∧ η≤1/7 ∧ η≤gap/50 ∧
      0<τ ∧ τ≤gap/50 ∧ 0<π ∧ 0<eps ∧ 0<loss ∧
      ρ+15*η+π+eps+loss≤εm:=by
  let ρ:=min (εm/4) (1/4)
  have hρ:0<ρ:=lt_min (by linarith) (by norm_num)
  have hρa:ρ≤εm/4:=min_le_left _ _
  have hρb:ρ≤1/4:=min_le_right _ _
  refine ⟨ρ,ρ/4,ρ/400,ρ/400,ρ/16,ρ/16,ρ/16,hρ,hρb,hρa,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
end OAI.SevenEighths.InverseInitialMarkedReserve
