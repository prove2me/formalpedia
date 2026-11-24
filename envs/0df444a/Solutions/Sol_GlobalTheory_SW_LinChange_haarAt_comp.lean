-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.haarAt_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:57:12.422221+00:00
-- url     : https://prove2.me/submissions/827d95d6-e391-490d-a523-3fe25928fca5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_finsum_quot_le
import Theorems.Thm_GlobalTheory_SW_LinChange_finsum_quot_map
import Theorems.Thm_GlobalTheory_SW_LinChange_map_perSub_le
import Theorems.Thm_GlobalTheory_SW_LinChange_relIndex_map
import Theorems.Thm_GlobalTheory_SW_LinChange_periodic_of_level

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
theorem _root_.solution (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (R M : ℕ) (hR : 0 < R) (hM : 0 < M)
    (hT : ∀ y, IntM y → IntM ((M : K) • T y)) (φ : Matrix κ ι K → ℂ) (h : HasLevel R φ) :
    haarAt (R * M) (fun x => φ (T x)) =
      ((|LinearMap.det T.toLinearMap| : ℚ) : ℂ) * haarAt R φ := by
  have hi := relIndex_map T R M hR hM hT
  have hle := map_perSub_le T R M hT
  have hd : LinearMap.det T.toLinearMap ≠ 0 := T.isUnit_det'.ne_zero
  have hne : ((perSub K κ ι (R * M)).map T.toAddEquiv.toAddMonoidHom).relIndex
      (perSub K κ ι R) ≠ 0 := by
    intro h0
    rw [h0] at hi
    have : (0 : ℚ) < (M : ℚ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) *
        |LinearMap.det T.toLinearMap| := by positivity
    rw [← hi] at this
    simp at this
  have e1 := finsum_quot_map (perSub K κ ι (R * M)) T.toAddEquiv φ
    fun x y hy => periodic_of_level h x y (hle hy)
  have e2 := finsum_quot_le _ _ hle hne φ (periodic_of_level h)
  have hi' := congrArg (fun t : ℚ => (t : ℂ)) hi
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow] at hi'
  unfold haarAt
  erw [e1]
  rw [e2, hi']
  have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  push_cast
  rw [mul_pow]
  field_simp
end GlobalTheory.SW.LinChange
