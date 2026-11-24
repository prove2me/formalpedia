-- Prove2me | solution 1 for GlobalTheory.InjHol.localStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:04:41.885149+00:00
-- url     : https://prove2.me/submissions/a6232286-f7f9-4833-b516-6f845dcc3258

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Theorems.Thm_GlobalTheory_InjHol_not_injOn_of_fderiv_eq_zero
import Theorems.Thm_GlobalTheory_InjHol_deriv_ne_zero_of_injOn
import Theorems.Thm_GlobalTheory_InjHol_exists_slice
import Theorems.Thm_GlobalTheory_InjHol_eventually_zero_of_subset
import Theorems.Thm_GlobalTheory_InjHol_exists_regular_of_zero
import Theorems.Thm_GlobalTheory_InjHol_analyticAt_det
import Theorems.Thm_GlobalTheory_InjHol_injective_of_fderiv_ne_zero
import Theorems.Thm_GlobalTheory_AnalyticMatrixEntries_analyticAt_det


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
theorem _root_.solution (n : ℕ) : LocalStatement n := by
  induction n with
  | zero =>
    intro E F _ _ _ _ _ _ hE _ f a _ _
    haveI : Subsingleton E := Module.finrank_zero_iff.mp hE
    exact Function.injective_of_subsingleton _
  | succ n ih =>
    rintro E F _ _ _ _ _ _ hE hF f a hf ⟨s, hs, hinj⟩
    haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
    haveI : CompleteSpace F := FiniteDimensional.complete ℂ F
    haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    refine injective_of_fderiv_ne_zero ih hE hF hf hs hinj fun h0 => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨eE⟩ : Nonempty (ℂ ≃L[ℂ] E) :=
        FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simp [hE])
      obtain ⟨eF⟩ : Nonempty (F ≃L[ℂ] ℂ) :=
        FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simp [hF])
      obtain ⟨c, rfl⟩ := eE.surjective a
      refine deriv_ne_zero_of_injOn (f := fun t => eF (f (eE t))) (a := c)
        ((eF.analyticAt _).comp (hf.comp (eE.analyticAt _)))
        (eE.continuous.continuousAt.preimage_mem_nhds hs)
        (fun x hx y hy hxy => eE.injective (hinj hx hy (eF.injective hxy))) ?_
      have := (eF.hasFDerivAt.comp c
        (hf.differentiableAt.hasFDerivAt.comp c eE.hasFDerivAt)).hasDerivAt.deriv
      refine this.trans ?_
      simp [h0]
    · obtain ⟨e⟩ : Nonempty (F ≃L[ℂ] E) :=
        FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (hF.trans hE.symm)
      let A : E → E →L[ℂ] E := fun z => (e : F →L[ℂ] E).comp (fderiv ℂ f z)
      let h : E → ℂ := fun z => LinearMap.det (A z : E →ₗ[ℂ] E)
      have hh : AnalyticAt ℂ h a :=
        analyticAt_det (((ContinuousLinearMap.compL ℂ E F E (e : F →L[ℂ] E)).analyticAt _).comp
          hf.fderiv)
      have hW : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ f z ∧ s ∈ 𝓝 z :=
        hf.eventually_analyticAt.and (eventually_mem_nhds_iff.mpr hs)
      have hZ : ∀ z, AnalyticAt ℂ f z ∧ s ∈ 𝓝 z → h z = 0 → fderiv ℂ f z = 0 := by
        intro z hz hz0
        by_contra hne
        have hi := injective_of_fderiv_ne_zero ih hE hF hz.1 hz.2 hinj hne
        exact LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz0
          (LinearMap.ker_eq_bot.mpr (e.injective.comp hi))
      have ha : h a = 0 := by
        refine LinearMap.det_eq_zero_iff_ker_ne_bot.mpr ?_
        simp [A, h0]
      have hne : ¬ ∀ᶠ z in 𝓝 a, h z = 0 := fun hc =>
        not_injOn_of_fderiv_eq_zero hf (by filter_upwards [hW, hc] using hZ) hs hinj
      obtain ⟨b, hb, hb0, hhb, g, hg, hg0, hsub⟩ := exists_regular_of_zero hh ha hne hW
      have hgb : g b = 0 := hsub.self_of_nhds hb0
      have hfill := eventually_zero_of_subset hg hhb hg0 hb0 hsub
      obtain ⟨ψ, hψ, hψ0, -, hψg, t, ht, hψi⟩ :=
        exists_slice hg hg.differentiableAt.hasFDerivAt hg0
      haveI : Nontrivial (fderiv ℂ g b).ker := by
        have := Module.Dual.finrank_ker_add_one_of_ne_zero
          (f := (fderiv ℂ g b : E →ₗ[ℂ] ℂ)) (fun h => hg0 (ContinuousLinearMap.coe_injective h))
        exact Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
      have hT : Tendsto ψ (𝓝 0) (𝓝 b) := by
        have := hψ.continuousAt.tendsto
        rwa [hψ0] at this
      have hWb : ∀ᶠ z in 𝓝 b, AnalyticAt ℂ f z ∧ s ∈ 𝓝 z :=
        hb.1.eventually_analyticAt.and (eventually_mem_nhds_iff.mpr hb.2)
      refine not_injOn_of_fderiv_eq_zero (f := fun x => f (ψ x)) (hb.1.comp_of_eq hψ hψ0) ?_
        (inter_mem ht (hT hb.2)) fun x hx y hy hxy => hψi hx.1 hy.1 (hinj hx.2 hy.2 hxy)
      filter_upwards [hT.eventually hWb, hT.eventually hfill, hψg, hψ.eventually_analyticAt]
        with x h1 h2 h3 h4
      have := (h1.1.differentiableAt.hasFDerivAt.comp x h4.differentiableAt.hasFDerivAt).fderiv
      refine this.trans ?_
      simp [hZ _ h1 (h2 (h3.trans hgb))]
end GlobalTheory.InjHol
