-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PolyGaussSchwartz.eval_temperate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:10:50.996342+00:00
-- url     : https://prove2.me/submissions/5117bc56-0909-44b5-b15a-a6fd2e04bd61

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzPolyMulGauss
import Theorems.Thm_GlobalTheory_CompanionTheory_PolyGaussSchwartz_coord_temperate
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PolyGaussSchwartz
variable {m n : ℕ}
namespace GlobalTheory.CompanionTheory.PolyGaussSchwartz
theorem _root_.solution (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun u => MvPolynomial.eval (fun k => coord k u) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (MvPolynomial.C a)) = fun _ => a := by
      funext u; simp
    rw [this]; exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun u : Fin m → Fin n → ℂ => MvPolynomial.eval (fun k => coord k u) (p + q)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p +
          MvPolynomial.eval (fun k => coord k u) q := by
      funext u; simp
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (p * MvPolynomial.X k)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p * coord k u := by
      funext u; simp
    rw [this]; exact hp.mul (coord_temperate k)
end GlobalTheory.CompanionTheory.PolyGaussSchwartz
