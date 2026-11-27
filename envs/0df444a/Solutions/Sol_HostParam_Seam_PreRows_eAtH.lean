-- Prove2me | solution 1 for HostParam.Seam.PreRows.eAtH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:23.665931+00:00
-- url     : https://prove2.me/submissions/4afe99cd-728c-4c9b-9d31-e89cee722c05

import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_MemRealCyclotomicSubgroup
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_OfPInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC Formalism.FrobeniusOrbits
noncomputable section
open HostParam HostParam.Seam
namespace HostParam.Seam
namespace PreRows
theorem _root_.solution {T : HType} {κ : HConst} {X x : ℝ} {φ : Frame} {H : HostRaw φ} {rr rr' : ℕ}
    (hr : PreRows T κ X x H rr rr') (hC : 0 ≤ κ.C) (h : Formalism.HC.HostConditions T κ X x H) {TT : Finset φ.A}
    (hs : φ.Shares TT (x ^ (-1 + T.eps))) : EAtH (T.level φ.o) H TT x T.eps (κ.C * T.J) := by
  refine ⟨rfl, h.kept, h.e, hs, h.c1, fun θ hθ N _ χ hχ => (h.b.2 θ hθ N χ hχ).trans ?_⟩
  have h1 := hr.one_le_X
  have hJ : (0 : ℝ) < T.J := by exact_mod_cast T.one_le_J
  have h3 := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hr.x_ge
  rw [Real.log_rpow (by linarith), div_mul_eq_mul_div, one_mul, div_le_iff₀ hJ] at h3
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) hC
end PreRows
end HostParam.Seam
