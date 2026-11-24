-- Prove2me | solution 1 for GlobalTheory.InjHol.exists_slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:52.797537+00:00
-- url     : https://prove2.me/submissions/73773e85-adbc-43ae-bbf0-e61ebf9113b5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Theorems.Thm_GlobalTheory_InjHol_exists_apply_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Metric Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.InjHol
namespace GlobalTheory.InjHol
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {g : E → ℂ} {b : E} (hg : AnalyticAt ℂ g b) {L : E →L[ℂ] ℂ} (hL : HasFDerivAt g L b)
    (h0 : L ≠ 0) :
    ∃ ψ : L.ker → E, AnalyticAt ℂ ψ 0 ∧ ψ 0 = b ∧ HasFDerivAt ψ L.ker.subtypeL 0 ∧
      (∀ᶠ x in 𝓝 0, g (ψ x) = g b) ∧ ∃ s ∈ 𝓝 (0 : L.ker), InjOn ψ s := by
  obtain ⟨v, hv⟩ := exists_apply_eq_one h0
  let R : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ v
  have hR : Function.RightInverse R L := fun t => by simp [R, hv]
  let p := L.projKerOfRightInverse R hR
  let e : E ≃L[ℂ] ℂ × L.ker := ContinuousLinearEquiv.equivOfRightInverse L R hR
  let G : E → ℂ × L.ker := fun x => (g x, p (x - b))
  have hG : ContDiffAt ℂ ω G b :=
    (hg.prod ((p.analyticAt _).comp (analyticAt_id.sub analyticAt_const))).contDiffAt
  have hG' : HasFDerivAt G (e : E →L[ℂ] ℂ × L.ker) b := by
    have := hL.prodMk (p.hasFDerivAt.comp b ((hasFDerivAt_id b).sub_const b))
    exact this
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hGb : G b = (g b, 0) := by simp [G]
  let I := hG.localInverse hG' hω
  have hI : AnalyticAt ℂ I (g b, 0) := hGb ▸ (hG.to_localInverse hG' hω).analyticAt
  have hI0 : I (g b, 0) = b := hGb ▸ hG.localInverse_apply_image hG' hω
  have hI' : HasFDerivAt I (e.symm : ℂ × L.ker →L[ℂ] E) (g b, 0) :=
    hGb ▸ (hG.hasStrictFDerivAt' hG' hω).to_localInverse.hasFDerivAt
  have hri : ∀ᶠ y in 𝓝 (g b, (0 : L.ker)), G (I y) = y :=
    hGb ▸ (hG.hasStrictFDerivAt' hG' hω).eventually_right_inverse
  have hc : ContinuousAt (fun x : L.ker => (g b, x)) 0 := by fun_prop
  have hri' := hc.eventually hri
  refine ⟨fun x => I (g b, x), ?_, hI0, ?_, ?_, _, hri', ?_⟩
  · exact hI.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  · have := HasFDerivAt.comp (0 : L.ker) (f := fun x : L.ker => (g b, x)) hI'
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) (g b) (0 : L.ker))
    convert! this
    ext x
    simp [e]
  · filter_upwards [hri'] with x hx
    exact congrArg Prod.fst hx
  · intro x hx y hy hxy
    have h1 : G (I (g b, x)) = (g b, x) := hx
    have h2 : G (I (g b, y)) = (g b, y) := hy
    have h3 : I (g b, x) = I (g b, y) := hxy
    rw [h3, h2] at h1
    exact (congrArg Prod.snd h1).symm
end GlobalTheory.InjHol
