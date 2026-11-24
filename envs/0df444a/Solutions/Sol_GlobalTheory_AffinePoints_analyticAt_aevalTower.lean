-- Prove2me | solution 1 for GlobalTheory.AffinePoints.analyticAt_aevalTower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:36.626701+00:00
-- url     : https://prove2.me/submissions/af872825-644c-492f-b1ac-6c8da1444ba7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
namespace GlobalTheory.AffinePoints
theorem _root_.solution {σ ι : Type*} [Fintype σ] [Fintype ι]
    (q : MvPolynomial ι (MvPolynomial σ 𝕜)) (w : (σ → 𝕜) × (ι → 𝕜)) :
    AnalyticAt 𝕜 (fun w : (σ → 𝕜) × (ι → 𝕜) =>
      (aevalTower (aeval w.1) w.2 : MvPolynomial ι (MvPolynomial σ 𝕜) →ₐ[𝕜] 𝕜) q) w := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp only [aevalTower_C]
    exact AnalyticAt.aeval_mvPolynomial (A := 𝕜) (f := fun w : (σ → 𝕜) × (ι → 𝕜) => w.1)
      (fun i => ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) i).comp
        (ContinuousLinearMap.fst 𝕜 (σ → 𝕜) (ι → 𝕜))).analyticAt w) a
  | add P Q hP hQ => simp only [map_add]; exact hP.add hQ
  | mul_X P i hP =>
    simp only [map_mul, aevalTower_X]
    exact hP.mul (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) i).comp
        (ContinuousLinearMap.snd 𝕜 (σ → 𝕜) (ι → 𝕜))).analyticAt w)
end GlobalTheory.AffinePoints
