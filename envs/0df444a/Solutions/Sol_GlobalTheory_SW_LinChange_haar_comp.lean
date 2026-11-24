-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.haar_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:36:16.501414+00:00
-- url     : https://prove2.me/submissions/37993027-bf66-4c1d-8f72-3f915193eb47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_intM_nat_smul
import Theorems.Thm_GlobalTheory_SW_LinChange_exists_den
import Theorems.Thm_GlobalTheory_SW_LinChange_map_nat_smul
import Theorems.Thm_GlobalTheory_SW_LinChange_haarAt_comp
import Theorems.Thm_GlobalTheory_SW_LinChange_haar_eq_haarAt

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
theorem _root_.solution (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (φ : Matrix κ ι K → ℂ) (hφ : IsSB φ) :
    IsSB (fun x => φ (T x)) ∧
      haar (fun x => φ (T x)) = ((|LinearMap.det T.toLinearMap| : ℚ) : ℂ) * haar φ := by
  obtain ⟨R, hR, h⟩ := hφ
  obtain ⟨M, hM, hT⟩ := exists_den T.toLinearMap
  obtain ⟨N, hN, hT'⟩ := exists_den T.symm.toLinearMap
  have hT2 : ∀ y, IntM y → IntM (((N * M : ℕ) : K) • T y) := fun y hy => by
    rw [Nat.cast_mul, mul_smul]
    exact intM_nat_smul N (hT y hy)
  have hl : HasLevel (R * (N * M)) (fun x => φ (T x)) := by
    refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
    · have := intM_nat_smul M (hT' _ (h.1 _ hx))
      rw [map_nat_smul] at this
      simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, smul_smul] at this
      convert this using 2
      push_cast; ring
    · have := h.2 (T x) _ (hT2 y hy)
      rw [smul_smul, ← Nat.cast_mul] at this
      simp only [map_add]
      rw [← this]
      congr 2
      exact map_nat_smul T.toLinearMap _ _
  have hp : 0 < R * (N * M) := by positivity
  refine ⟨⟨_, hp, hl⟩, ?_⟩
  rw [haar_eq_haarAt hp hl, haar_eq_haarAt hR h, haarAt_comp T R _ hR (by positivity) hT2 φ h]
end GlobalTheory.SW.LinChange
