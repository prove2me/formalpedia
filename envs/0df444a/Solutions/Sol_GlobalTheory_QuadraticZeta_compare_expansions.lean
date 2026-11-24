-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.compare_expansions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:08.913067+00:00
-- url     : https://prove2.me/submissions/add5b37b-cd37-4beb-9353-454d69bf1660

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
open GlobalTheory.QuadraticZeta
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution {L : ℂ → ℂ} (hL : DifferentiableAt ℂ L 1) {A : ℝ → ℝ} {a C c : ℝ}
    (hc : 0 < c) (hA : Tendsto (fun s => A s - a / (s - 1)) (𝓝[>] 1) (𝓝 C))
    (h : ∀ s : ℝ, 1 < s → riemannZeta s * L s = (c ^ s / 2 * A s : ℝ)) :
    L 1 = (c / 2 * a : ℝ) ∧
      Real.eulerMascheroniConstant * L 1 + deriv L 1 = (c / 2 * (C + a * Real.log c) : ℝ) := by
  have hu := ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right
  have hB := (Complex.continuous_ofReal.tendsto _).comp hA
  have dL : HasDerivAt (fun s : ℝ => L s) (deriv L 1) 1 :=
    HasDerivAt.comp_ofReal (by simpa using hL.hasDerivAt)
  have dG : HasDerivAt (fun s : ℝ => ((c ^ s / 2 : ℝ) : ℂ)) (c * Real.log c / 2 : ℝ) 1 := by
    simpa using ((Real.hasStrictDerivAt_const_rpow hc 1).hasDerivAt.div_const 2).ofReal_comp
  have hle : 𝓝[>] (1 : ℝ) ≤ 𝓝[≠] 1 := nhdsWithin_mono _ fun _ h => ne_of_gt h
  have cL := dL.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have cG := dG.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have sL := (hasDerivAt_iff_tendsto_slope.1 dL).mono_left hle
  have sG := (hasDerivAt_iff_tendsto_slope.1 dG).mono_left hle
  have c0 : Tendsto (fun s : ℝ => (s - 1 : ℂ)) (𝓝[>] 1) (𝓝 0) := by
    have : Continuous fun s : ℝ => (s - 1 : ℂ) := by fun_prop
    simpa using (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have hne : ∀ s : ℝ, 1 < s → (s - 1 : ℂ) ≠ 0 := fun s hs => by
    exact_mod_cast (sub_pos.2 hs).ne'
  have e1 : L 1 = (c / 2 * a : ℝ) := by
    have := tendsto_nhds_unique_of_eventuallyEq (((c0.mul hu).add_const 1).mul cL)
      (cG.mul ((c0.mul hB).add_const (a : ℂ))) (by
        filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
        have h1 := h s hs
        have h2 := hne s hs
        simp only [Function.comp_apply]
        push_cast at h1 ⊢
        field_simp
        linear_combination 2 * (s - 1) * h1)
    simpa using this
  refine ⟨e1, ?_⟩
  have := tendsto_nhds_unique_of_eventuallyEq ((hu.mul cL).add sL)
    ((cG.mul hB).add (sG.const_mul (a : ℂ))) (by
      filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      have h1 := h s hs
      have h2 := hne s hs
      simp only [Function.comp_apply, slope, vsub_eq_sub, Complex.real_smul, Complex.ofReal_one,
        e1, Real.rpow_one]
      push_cast at h1 ⊢
      field_simp
      linear_combination 2 * (s - 1) * h1)
  simp only [Complex.ofReal_one, Real.rpow_one] at this
  rw [this]
  push_cast
  ring
end GlobalTheory.QuadraticZeta
