-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:30.153686+00:00
-- url     : https://prove2.me/submissions/066e23ea-3205-4384-a6f1-f2f4cd070698

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_intM_add
import Theorems.Thm_GlobalTheory_SW_LinChange_exists_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.LinChange
theorem _root_.solution (T : Matrix κ ι K →ₗ[ℚ] Matrix κ ι K) :
    ∃ M : ℕ, 0 < M ∧ ∀ y, IntM y → IntM ((M : K) • T y) := by
  classical
  obtain ⟨J, _, _, b, hb⟩ := exists_basis (K := K) (κ := κ) (ι := ι)
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := K)
    (Finset.univ.image fun p : J × κ × ι => T (b p.1) p.2.1 p.2.2)
  refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, fun y hy => ?_⟩
  rw [← hb] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    intro k i
    have h := hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, k, i)))
    rw [Matrix.smul_apply, smul_eq_mul]
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq m with e | e
    · rw [e, Int.cast_natCast] at h; exact h
    · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at h; simpa using h.neg
  | zero => rw [map_zero, smul_zero]; exact fun _ _ => isIntegral_zero
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact intM_add hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact fun k i => (hx k i).neg
end GlobalTheory.SW.LinChange
