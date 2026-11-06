-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.initial_margins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:26.49528+00:00
-- url     : https://prove2.me/submissions/b07a6f30-3ff5-4143-822f-c8936e4ebd9c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic
import Theorems.Thm_OAI_SevenEighths_InverseMoment_initial_margins_sharp

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta)
    (hc : 0 ≤ min c₁ c₂) (hdelta : 0 ≤ delta) (heta : eta ≤ min c₁ c₂ / 100)
    (htau : tau ≤ min c₁ c₂ / 100) :
    CanonicalMargins (initialF r z G P delta)
      (initialM m r z G P eta tau) Q (z - G) (3 * min c₁ c₂ / 4) := by
  obtain ⟨ha, hb⟩ := initial_margins_sharp (delta := delta) (tau := tau) h₁ h₂ hG hP hQ
  have hc₁ := min_le_left c₁ c₂
  have hc₂ := min_le_right c₁ c₂
  constructor <;> linarith
end OAI.SevenEighths.InverseMoment
