-- Prove2me | solution 1 for GlobalTheory.IntegerScalarIntegral.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:04:40.903078+00:00
-- url     : https://prove2.me/submissions/e3c2077c-2841-4fe0-af65-6d782d447b7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntSmulIntegral
import Theorems.Thm_GlobalTheory_IntegerScalarIntegral_exists_int_smul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IntegerScalarIntegral
open NumberField
namespace GlobalTheory.IntegerScalarIntegral
theorem _root_.solution {K : Type u_1} {V : Type u_2} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ m : ℤ, m ≠ 0 ∧ m • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hbz a
  | smul c x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_smul_integral c
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    let r : 𝓞 K := ⟨d • c, hint⟩
    have hr : (algebraMap (𝓞 K) K r) = d • c := rfl
    have key : (d * m) • (c • x) = r • (m • x) := by
      rw [← algebraMap_smul K r (m • x), hr, smul_comm (d • c) m x, smul_assoc, mul_comm, mul_smul]
    rw [key]
    exact L.smul_mem r hmx
end GlobalTheory.IntegerScalarIntegral
