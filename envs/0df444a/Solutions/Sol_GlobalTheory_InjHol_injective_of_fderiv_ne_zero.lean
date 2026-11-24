-- Prove2me | solution 1 for GlobalTheory.InjHol.injective_of_fderiv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:51.152352+00:00
-- url     : https://prove2.me/submissions/62554414-8695-4314-87fb-a3fb44af3b0c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Theorems.Thm_GlobalTheory_InjHol_exists_apply_eq_one
import Theorems.Thm_GlobalTheory_InjHol_exists_slice

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
theorem _root_.solution {n : ℕ} (ih : LocalStatement n) {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (hE : Module.finrank ℂ E = n + 1) (hF : Module.finrank ℂ F = n + 1) {f : E → F} {a : E}
    (hf : AnalyticAt ℂ f a) {s : Set E} (hs : s ∈ 𝓝 a) (hinj : InjOn f s)
    (h0 : fderiv ℂ f a ≠ 0) : Function.Injective (fderiv ℂ f a) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨w, hw⟩ : ∃ w, fderiv ℂ f a w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (ContinuousLinearMap.ext hc)
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_ne_zero ℂ hw
  let l : F →L[ℂ] ℂ := LinearMap.toContinuousLinearMap l₀
  have hL0 : l.comp (fderiv ℂ f a) ≠ 0 := fun h => hl₀ (congrArg (fun T => T w) h)
  have hl0 : l ≠ 0 := fun h => hL0 (by simp [h])
  obtain ⟨ψ, hψ, hψ0, hψ', hψg, t, ht, hψi⟩ := exists_slice (g := fun x => l (f x))
    ((l.analyticAt _).comp hf) (l.hasFDerivAt.comp a hf.differentiableAt.hasFDerivAt) hL0
  obtain ⟨u, hu⟩ := exists_apply_eq_one hl0
  let R : ℂ →L[ℂ] F := ContinuousLinearMap.toSpanSingleton ℂ u
  have hR : Function.RightInverse R l := fun t => by simp [R, hu]
  let p := l.projKerOfRightInverse R hR
  have hK : Module.finrank ℂ (l.comp (fderiv ℂ f a)).ker = n := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero
      (f := (l.comp (fderiv ℂ f a) : E →ₗ[ℂ] ℂ)) (fun h => hL0 (ContinuousLinearMap.coe_injective h))
    omega
  have hK' : Module.finrank ℂ l.ker = n := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero
      (f := (l : F →ₗ[ℂ] ℂ)) (fun h => hl0 (ContinuousLinearMap.coe_injective h))
    omega
  have hs' : ∀ᶠ x in 𝓝 0, ψ x ∈ s := hψ.continuousAt.eventually (by rw [hψ0]; exact hs)
  have hfa : HasFDerivAt f (fderiv ℂ f a) (ψ 0) := by
    rw [hψ0]
    exact hf.differentiableAt.hasFDerivAt
  have key := ih _ _ hK hK' (fun x => p (f (ψ x))) 0
    ((p.analyticAt _).comp (hf.comp_of_eq hψ hψ0))
    ⟨_, inter_mem ht (hs'.and hψg), fun x hx y hy hxy => by
      refine hψi hx.1 hy.1 (hinj hx.2.1 hy.2.1 ?_)
      have h1 : f (ψ x) - R (l (f (ψ x))) = f (ψ y) - R (l (f (ψ y))) := congrArg Subtype.val hxy
      rw [hx.2.2, hy.2.2] at h1
      exact sub_left_injective h1⟩
  have hd := (p.hasFDerivAt.comp 0 (hfa.comp 0 hψ')).fderiv
  rw [show fderiv ℂ (fun x => p (f (ψ x))) 0 = _ from hd] at key
  rw [injective_iff_map_eq_zero] at key ⊢
  intro x hx
  exact congrArg Subtype.val (key ⟨x, by simp [hx]⟩ (by
    change p (fderiv ℂ f a x) = 0
    rw [hx, map_zero]))
end GlobalTheory.InjHol
