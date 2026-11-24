-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.irreducible_of_val_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:13:21.456875+00:00
-- url     : https://prove2.me/submissions/127d8475-3ad7-4516-949f-832d79d521d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_mul_ne
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_irreducible
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_pow_ne
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_isUnit

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
theorem _root_.solution (K : UQ) {x : K.O} (hx : val K.O (algebraMap K.O K.E x) = 1) :
    Irreducible x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp [val] at hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hϖ0 : algebraMap K.O K.E ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have hu0 : algebraMap K.O K.E (u : K.O) ≠ 0 := by simp
  rw [map_mul, map_pow, val_mul_ne K hu0 (pow_ne_zero _ hϖ0), val_pow_ne K hϖ0,
    val_isUnit K u.isUnit, val_irreducible K hϖ] at hx
  have hn : n = 1 := by omega
  subst hn
  rw [pow_one]
  exact (irreducible_units_mul u).2 hϖ
end GlobalTheory.UnitLemma.Unr
