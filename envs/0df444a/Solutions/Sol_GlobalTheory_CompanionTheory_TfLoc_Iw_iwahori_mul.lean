-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:41:38.67138+00:00
-- url     : https://prove2.me/submissions/607057b4-bb1f-47e4-902a-eb6b6bfd95b0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_mem_unitGL_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {F : Type*} [Field F] [ValuativeRel F] {m : ℕ}
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution {g h : GL (Fin m) F} (hg : g ∈ iwahori (m := m) F) (hh : h ∈ iwahori (m := m) F) :
    g * h ∈ iwahori (m := m) F := by
  refine ⟨mul_mem hg.1 hh.1, fun i j hij => ?_⟩
  have hg1 := ((mem_unitGL_iff g).1 hg.1).1
  have hh1 := ((mem_unitGL_iff h).1 hh.1).1
  rw [Units.val_mul, Matrix.mul_apply]
  refine (valuation F).map_sum_lt one_ne_zero fun l _ => ?_
  rw [map_mul]
  rcases lt_or_ge l i with hl | hl
  · rw [mul_comm]
    exact mul_lt_one_of_le_of_lt_alt (hh1 l j) (hg.2 i l hl)
  · exact mul_lt_one_of_le_of_lt_alt (hg1 i l) (hh.2 l j (lt_of_lt_of_le hij hl))
end GlobalTheory.CompanionTheory.TfLoc.Iw
