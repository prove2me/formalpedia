-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:25:27.427336+00:00
-- url     : https://prove2.me/submissions/f6a8c551-3542-4318-9da2-58d68e8cf478

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleTraceAddCharNormEqOneNearZero
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NearZero_continuous_NL
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NearZero_NL_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.WeilQuad
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → {y : A.L | A.psiK ψ ((x : A.K) * A.NL y) = 1} ∈ 𝓝 (0 : A.L) := by
  intro F E _ _ _ _ _ A ψ x μ ω h
  obtain ⟨hK, hL, hψ, -, -⟩ := h
  let g : A.L → F := fun y => Algebra.trace F A.K ((x : A.K) * A.NL y)
  have hg : Continuous g := by
    have ht : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
    exact ht.comp (continuous_const.mul (NearZero.continuous_NL A hK))
  have hg0 : g 0 = 0 := by simp [g, NearZero.NL_zero A hK hL]
  have hmem : g ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : A.L) :=
    hg.continuousAt.preimage_mem_nhds (by rw [hg0]; exact Metric.ball_mem_nhds 0 one_pos)
  refine Filter.mem_of_superset hmem fun y hy => ?_
  have hy' : ‖g y‖ < 1 := by simpa using hy
  exact hψ.1 _ hy'.le
end GlobalTheory.JR.WeilQuad
