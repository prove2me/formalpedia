-- Prove2me | solution 1 for OAI.SevenEighths.Parameters.fine_slot_widths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:57.726206+00:00
-- url     : https://prove2.me/submissions/f2484343-7835-47f6-a49b-199cf103acc7

import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersHighData
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersHighDataFine

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.Parameters
namespace OAI.SevenEighths.Parameters
theorem _root_.solution {Δ:ℝ}(D:HighData Δ)(mesh:ℝ→ℝ)
    (hmesh:0<mesh D.t)(hfine:∀j,D.ell j≤mesh D.t/200)
    (d:ℝ)(hd:(1/200:ℝ)≤d)(j:Fin D.N):
    0<D.ell j/d ∧ D.ell j/d≤mesh D.t:=by
  have hd0:0<d:=by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0,(div_le_iff₀ hd0).mpr ?_⟩
  have hh:=hfine j
  nlinarith
end OAI.SevenEighths.Parameters
