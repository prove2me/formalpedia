-- Prove2me | solution 1 for GlobalTheory.InjHol.analyticAt_of_differentiableOn_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:16.798445+00:00
-- url     : https://prove2.me/submissions/6a177cbb-ff2a-483d-b0bd-457fa1cc3572

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHolomorphicLocalInverseOfInjOn
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.InjHol
namespace GlobalTheory.InjHol
theorem _root_.solution {n : ℕ} {W : Set (V n)} {g : V n → V n} {a : V n}
    (hW : IsOpen W) (ha : a ∈ W) (hg : DifferentiableOn ℂ g W) : AnalyticAt ℂ g a := by
  let e : V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU : IsOpen (e.symm ⁻¹' W) := hW.preimage e.symm.continuous
  have hf : DifferentiableOn ℂ (fun x => e (g (e.symm x))) (e.symm ⁻¹' W) :=
    e.differentiable.comp_differentiableOn
      (hg.comp e.symm.differentiable.differentiableOn (fun _ hx => hx))
  have ha' : e a ∈ e.symm ⁻¹' W := by simpa using ha
  have han : AnalyticAt ℂ (fun x => e (g (e.symm x))) (e a) := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n _ (fun x => e (g (e.symm x)) i) hU
      (differentiableOn_pi.mp hf i) _ ha'
  have h2 : AnalyticAt ℂ (fun y => e.symm (e (g (e.symm (e y))))) a :=
    ((e.symm : (Fin n → ℂ) →L[ℂ] V n).analyticAt _).comp
      (han.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt a))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h2
end GlobalTheory.InjHol
