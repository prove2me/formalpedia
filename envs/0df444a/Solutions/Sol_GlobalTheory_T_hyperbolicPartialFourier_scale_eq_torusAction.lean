-- Prove2me | solution 1 for GlobalTheory.T.hyperbolicPartialFourier_scale_eq_torusAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:30.672796+00:00
-- url     : https://prove2.me/submissions/f18709a1-d0cb-4837-991f-d955080b49d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierScaleEqTorusAction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierScaleEqTorusActionStatement
import Theorems.Thm_GlobalTheory_JR_Hyp_pt_scale_eq_rg_mS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ) (x : A.K) (s : A.Kˣ) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => (A.absK (s : A.K) : ℂ) * Φ ((s : A.K) * p.1, (s : A.K) * p.2)) = Hyp.rg A (mS s) (Hyp.pt A ν ψ x Φ) := by
  first | exact @GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS | exact GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS | (intros; apply GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS <;> assumption)
end _root_.GlobalTheory.T
