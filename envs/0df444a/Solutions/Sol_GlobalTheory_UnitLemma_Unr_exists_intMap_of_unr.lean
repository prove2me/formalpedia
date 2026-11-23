-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.exists_intMap_of_unr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:00.978572+00:00
-- url     : https://prove2.me/submissions/50a58daa-3add-4df2-b4e3-f43b2ebe0685

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_int_image


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
open GlobalTheory.UnitLemma IsDedekindDomain IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (hU : IsUnrExt K K' d φ) :
    ∃ ψ : K.O →+* K'.O, ∀ a, algebraMap K'.O K'.E (ψ a) = φ (algebraMap K.O K.E a) := by
  choose f hf using exists_int_image hU
  have inj := IsFractionRing.injective K'.O K'.E
  let ψ : K.O →+* K'.O :=
    { toFun := f, map_one' := inj (by simp only [hf, map_one]),
      map_mul' := fun a b => inj (by simp only [hf, map_mul]),
      map_zero' := inj (by simp only [hf, map_zero]),
      map_add' := fun a b => inj (by simp only [hf, map_add]) }
  exact ⟨ψ, hf⟩
end GlobalTheory.UnitLemma.Unr
