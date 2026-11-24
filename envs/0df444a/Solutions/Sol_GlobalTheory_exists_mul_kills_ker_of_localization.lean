-- Prove2me | solution 1 for GlobalTheory.exists_mul_kills_ker_of_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:59.161117+00:00
-- url     : https://prove2.me/submissions/5883a23a-618a-496e-a7b3-4e220e859702

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetNotMemSpanMulVecOfSocle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIntegralOfLocalPresentationPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O H : Type) [CommRing O] [CommRing H] [Algebra O H]
    [Module.Finite O H] (ε : H →ₐ[O] O) (M : Submonoid H) (T : Type) [CommRing T] [Algebra H T]
    [IsLocalization M T] (u : H) (hu : ∀ h, ε h = 0 → algebraMap H T (h * u) = 0) :
    ∃ s : M, ∀ h, ε h = 0 → h * (s * u) = 0 := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := O) (M := H)
  have h1 : ∀ b : H, ∃ s : M, (s : H) * ((b - algebraMap O H (ε b)) * u) = 0 := fun b =>
    (IsLocalization.map_eq_zero_iff M T _).1 (hu _ (by simp))
  choose s hs using h1
  refine ⟨∏ b ∈ G, s b, fun h hh => ?_⟩
  have key : ∀ h : H, (h - algebraMap O H (ε h)) * (((∏ b ∈ G, s b : M) : H) * u) = 0 := by
    intro h
    have hmem : h ∈ Submodule.span O (G : Set H) := by rw [hG]; trivial
    induction hmem using Submodule.span_induction with
    | mem b hb =>
      rw [← Finset.mul_prod_erase G s hb, Submonoid.coe_mul]
      linear_combination ((∏ x ∈ G.erase b, s x : M) : H) * hs b
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add, map_add]
      linear_combination ha + hb
    | smul c a _ ha =>
      rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
      linear_combination algebraMap O H c * ha
  simpa [hh] using key h
end GlobalTheory
