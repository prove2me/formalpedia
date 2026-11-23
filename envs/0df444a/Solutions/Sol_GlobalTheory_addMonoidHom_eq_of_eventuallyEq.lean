-- Prove2me | solution 1 for GlobalTheory.addMonoidHom_eq_of_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:05.55626+00:00
-- url     : https://prove2.me/submissions/88737d09-7fa3-48e5-b1cf-849bf414fc6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Metric Set Filter Asymptotics
open scoped Topology
namespace GlobalTheory
section Taylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
end Taylor
section Halving
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ε : V → V} {r C : ℝ}
variable [CompleteSpace V]
end Halving
section Extension
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]
private theorem eventually_half_pow_smul_mem {s : Set V} (hs : s ∈ 𝓝 (0 : V)) (v : V) :
    ∀ᶠ j : ℕ in atTop, (2⁻¹ : ℝ) ^ j • v ∈ s := by
  have : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • v) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const v
  exact this.eventually hs
end Extension
end GlobalTheory
end

set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]
namespace GlobalTheory
theorem _root_.solution {e e' : V →+ A} (h : e =ᶠ[𝓝 0] e') : e = e' := by
  ext v
  obtain ⟨j, hj⟩ := (eventually_half_pow_smul_mem h v).exists
  have hv : v = (2 ^ j : ℕ) • (2⁻¹ : ℝ) ^ j • v := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp
  rw [hv, map_nsmul, map_nsmul, show e _ = e' _ from hj]
end GlobalTheory
