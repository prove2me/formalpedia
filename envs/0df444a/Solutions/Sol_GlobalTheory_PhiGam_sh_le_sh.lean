-- Prove2me | solution 1 for GlobalTheory.PhiGam.sh_le_sh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:27:09.20955+00:00
-- url     : https://prove2.me/submissions/ac0d2984-90d1-466b-a4ab-9b401ee4cff1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
variable [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]
namespace GlobalTheory.PhiGam
theorem _root_.solution (a : ℤ) {N N' : Submodule k⟦X⟧ V} (h : N ≤ N') : sh a N ≤ sh a N' :=
  Submodule.map_mono h
end GlobalTheory.PhiGam
