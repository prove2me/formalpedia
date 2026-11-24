-- Prove2me | solution 1 for GlobalTheory.GaussTransport.hasTemperateGrowth_chirp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:11:12.394831+00:00
-- url     : https://prove2.me/submissions/5aa2364d-fc4a-4d46-aef2-692ec0fdf66b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzDensityTransportLinearEquivChirp
import Theorems.Thm_GlobalTheory_GaussTransport_hasTemperateGrowth_expI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GaussTransport
namespace GlobalTheory.GaussTransport
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (s : ℝ) :
    Function.HasTemperateGrowth (fun x : V => Complex.exp (Complex.I * ((s * (Q x x).im : ℝ) : ℂ))) := by
  have h1 : Function.HasTemperateGrowth (fun x : V => Q x x) :=
    Q.bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' Function.HasTemperateGrowth.id'
  have h2 : Function.HasTemperateGrowth (fun x : V => s * (Q x x).im) := by
    have := ((s • Complex.imCLM : ℂ →L[ℝ] ℝ)).hasTemperateGrowth.comp h1
    simpa [Function.comp_def] using this
  exact hasTemperateGrowth_expI.comp h2
end GlobalTheory.GaussTransport
