-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.eta_det_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:05.135745+00:00
-- url     : https://prove2.me/submissions/8105a9fd-48c4-4e6f-9c32-f73278d33086

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportJacquetRallisDesc
import Theorems.Thm_GlobalTheory_JR_LinDesc_norm_eq_of_sub_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] (r : ℕ) :
    IsLocallyConstant (fun g : GL (Fin r) F => eta ((g : Matrix (Fin r) (Fin r) F).det)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hd : ((g : Matrix (Fin r) (Fin r) F).det) ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hc : Continuous (fun h : GL (Fin r) F => (h : Matrix (Fin r) (Fin r) F).det) :=
    Units.continuous_val.matrix_det
  have hpos : 0 < ‖(g : Matrix (Fin r) (Fin r) F).det‖ := norm_pos_iff.mpr hd
  have hev : ∀ᶠ h : GL (Fin r) F in 𝓝 g, ‖((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det - (g : Matrix (Fin r) (Fin r) F).det‖ <
      ‖(g : Matrix (Fin r) (Fin r) F).det‖ := by
    have : Continuous (fun h : GL (Fin r) F =>
        ‖(h : Matrix (Fin r) (Fin r) F).det - (g : Matrix (Fin r) (Fin r) F).det‖) :=
      (hc.sub continuous_const).norm
    exact (this.tendsto g).eventually_lt_const (by rw [sub_self, norm_zero]; exact hpos)
  filter_upwards [hev] with h hh
  unfold eta
  rw [norm_eq_of_sub_lt hh]
end GlobalTheory.JR.LinDesc
