-- Prove2me | solution 1 for GlobalTheory.PhiGam.nab_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:09.430373+00:00
-- url     : https://prove2.me/submissions/eed018b9-9030-4c5a-87e8-a32f580dde2c

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
namespace GlobalTheory.PhiGam
theorem _root_.solution [Module k V] [IsScalarTower k k⸨X⸩ V] (g : V →ₗ[k] V) (x : V) :
    nab g x = (vv k)⁻¹ • (g x - x) := rfl
end GlobalTheory.PhiGam
