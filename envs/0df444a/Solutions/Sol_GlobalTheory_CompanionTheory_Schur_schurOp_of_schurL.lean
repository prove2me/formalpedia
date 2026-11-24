-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Schur.schurOp_of_schurL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:08.870715+00:00
-- url     : https://prove2.me/submissions/7e77e6fb-0c0d-43c3-91eb-e231482a5ddb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchurOpOfSchurL
import Theorems.Thm_GlobalTheory_CompanionTheory_Schur_schur_memLp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Schur
open PositivityTheory.Rg.BcB.E1
variable {α : Type} [MeasurableSpace α] {ν : Measure α}
namespace GlobalTheory.CompanionTheory.Schur
theorem _root_.solution (hS : SchurL) : SchurOp := by
  intro α _ ν _ k A hk hA hr hc
  have H := fun f : Lp ℂ 2 ν => schur_memLp hS k A hk hA hr hc (f : α → ℂ) (Lp.memLp f)
  let L : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f => (H f).1.toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        have h1 := (H (f + g)).1.coeFn_toLp
        have h2 := (H f).1.coeFn_toLp
        have h3 := (H g).1.coeFn_toLp
        have h4 := Lp.coeFn_add ((H f).1.toLp _) ((H g).1.toLp _)
        filter_upwards [h1, h2, h3, h4, (H f).2.2, (H g).2.2] with x e1 e2 e3 e4 i1 i2
        rw [e1, e4, Pi.add_apply, e2, e3, ← integral_add i1 i2]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with y hy
        rw [hy, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        have h1 := (H (c • f)).1.coeFn_toLp
        have h2 := (H f).1.coeFn_toLp
        have h4 := Lp.coeFn_smul c ((H f).1.toLp _)
        filter_upwards [h1, h2, h4] with x e1 e2 e4
        rw [e1, RingHom.id_apply, e4, Pi.smul_apply, e2, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul]
        ring }
  refine ⟨L.mkContinuous A.toReal ?_, fun f => (H f).1.coeFn_toLp⟩
  intro f
  change ‖(H f).1.toLp _‖ ≤ A.toReal * ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hA (Lp.memLp f).2.ne) (H f).2.1
end GlobalTheory.CompanionTheory.Schur
