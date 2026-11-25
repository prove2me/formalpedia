-- Prove2me | solution 1 for GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:26.891337+00:00
-- url     : https://prove2.me/submissions/ecd9936f-d269-49e8-81f3-2d3ba2057f58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNeZeroSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonzeroSmulMem
open NumberField
namespace GlobalTheory.NonzeroSmulMem
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hay
    · rw [mul_smul]
      exact M.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨p, q, hq, hc⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap (𝓞 K) K q ≠ 0 := by
      intro h
      exact hq0 ((IsFractionRing.injective (𝓞 K) K) (by rw [h, map_zero]))
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h1 : q • (c • y) = p • y := by
      rw [← algebraMap_smul K q, ← algebraMap_smul K p, smul_smul, ← hc,
        mul_div_cancel₀ _ hqK]
    rw [mul_smul, h1, smul_smul, mul_comm, mul_smul]
    exact M.smul_mem p hay
end GlobalTheory.NonzeroSmulMem
