-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.val_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:51.863205+00:00
-- url     : https://prove2.me/submissions/3655f24e-0ffc-4aef-ae48-45fe13dd1e1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_mul_ne
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_algebraMap_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (K : UQ) {u : K.O} (hu : IsUnit u) : val K.O (algebraMap K.O K.E u) = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 : (algebraMap K.O K.E (w : K.O)) ≠ 0 := by simp
  have h2 : (algebraMap K.O K.E ((w⁻¹ : K.Oˣ) : K.O)) ≠ 0 := by simp
  have h := val_mul_ne K h1 h2
  rw [← map_mul, Units.mul_inv, map_one] at h
  have h3 := val_algebraMap_nonneg K (w : K.O)
  have h4 := val_algebraMap_nonneg K ((w⁻¹ : K.Oˣ) : K.O)
  have h5 : val K.O (1 : K.E) = 0 := by simp [val]
  omega
end GlobalTheory.UnitLemma.Unr
