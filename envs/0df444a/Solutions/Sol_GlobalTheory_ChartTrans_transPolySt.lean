-- Prove2me | solution 1 for GlobalTheory.ChartTrans.transPolySt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:05:09.677014+00:00
-- url     : https://prove2.me/submissions/6ee2fcba-1c43-4914-a6b4-04c66be81fd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Theorems.Thm_GlobalTheory_ChartTrans_ev_sum
import Theorems.Thm_GlobalTheory_ChartTrans_ev_C_mul
import Theorems.Thm_GlobalTheory_ChartTrans_dof_transF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.ChartTrans
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartTrans
theorem _root_.solution : TransPolySt := by
  intro k _ d F hF hu φ φi hinv ι _ u P g
  have hφ : GP φ := hinv.1
  have hit : ∀ (v : Fin d → k) (n : ℕ) (g : PS k 1 d),
      (Dof (transF F φ φi) v)^[n] (ev (n := 1) ![φ] g) =
        ev (n := 1) ![φ] ((Dof F ((dLin φ).mulVec v))^[n] g) := by
    intro v n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dof_transF F hF hu φ φi hinv, ih]
  have hmon : ∀ m : ι →₀ ℕ, DmonOf (transF F φ φi) u m (ev (n := 1) ![φ] g) =
      ev (n := 1) ![φ] (DmonOf F (fun l => (dLin φ).mulVec (u l)) m g) := by
    intro m
    unfold DmonOf
    induction (Finset.univ : Finset ι).toList with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  unfold DpolyOf
  rw [ev_sum _ (single_point_zero_constant hφ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_C_mul _ (single_point_zero_constant hφ), hmon]
end GlobalTheory.ChartTrans
