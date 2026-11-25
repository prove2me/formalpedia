-- Prove2me | solution 1 for LocBasisPlaceWork.span_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:43.203991+00:00
-- url     : https://prove2.me/submissions/d6bcbf13-ae8c-4fd3-a371-1f076c9238f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalBasisAtPrime_SpanClear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open LocBasisPlaceWork
namespace LocBasisPlaceWork
theorem _root_.solution {R A V : Type*} [CommRing R] [CommRing A] [Algebra R A] (M : Submonoid R)
    [IsLocalization M A] [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
    (S : Set V) : ∀ y ∈ span A S, ∃ s ∈ M, s • y ∈ span R S := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, M.one_mem, by rw [one_smul]; exact subset_span hx⟩
  | zero => exact ⟨1, M.one_mem, by rw [smul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, M.mul_mem hs ht, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact smul_mem _ _ hsx
    · rw [mul_smul]; exact smul_mem _ _ hty
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj M a
    refine ⟨(t : R) * s, M.mul_mem t.2 hs, ?_⟩
    have key : (t : R) • (a • x) = r • x := by
      rw [← algebraMap_smul A (t : R) (a • x), smul_smul, mul_comm (algebraMap R A _), e,
        algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_comm]
    exact smul_mem _ _ hsx
end LocBasisPlaceWork
