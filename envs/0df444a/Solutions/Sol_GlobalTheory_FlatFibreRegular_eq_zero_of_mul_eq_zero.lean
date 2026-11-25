-- Prove2me | solution 1 for GlobalTheory.FlatFibreRegular.eq_zero_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:59:26.513965+00:00
-- url     : https://prove2.me/submissions/3313cbc8-289c-40f4-9b7b-c781005366eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
import Theorems.Thm_GlobalTheory_FlatFibreRegular_mem_map_mul_of_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular
namespace GlobalTheory.FlatFibreRegular
theorem _root_.solution {A L : Type} [CommRing A] [IsNoetherianRing A] [CommRing L]
    [IsLocalRing L] [IsNoetherianRing L] [Algebra A L] [Module.Flat A L]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s))
    (hJ : 𝔭.map (algebraMap A L) ≠ ⊤)
    (g : L) (hg : ∀ y, g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L))
    (y : L) (hgy : g * y = 0) : y = 0 := by
  have hn : ∀ n : ℕ, y ∈ (𝔭 ^ n).map (algebraMap A L) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; exact Submodule.mem_top
    | succ n ih =>
      rw [pow_succ]
      exact mem_map_mul_of_mul_mem 𝔭 hu g hg (𝔭 ^ n) (IsNoetherian.noetherian _) y ih
        (by rw [hgy]; exact zero_mem _)
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ, Ideal.mem_iInf]
  intro n
  rw [← Ideal.map_pow]
  exact hn n
end GlobalTheory.FlatFibreRegular
