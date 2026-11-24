-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.IntBasis.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:48.594332+00:00
-- url     : https://prove2.me/submissions/634c9706-ec78-4f21-a102-c3c172ed59c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_adicVal_le_one_iff
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_adicVal_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.IntBasis
open IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr.IntBasis
theorem _root_.solution (h : IsUnrExt K K' d φ) :
    ∃ ι : K.O →+* K'.O, ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
  let S := (algebraMap K'.O K'.E).range
  have hS : ∀ a : K.O, (φ.comp (algebraMap K.O K.E)) a ∈ S := fun a => by
    obtain ⟨b, hb⟩ := (adicVal_le_one_iff K' (φ (algebraMap K.O K.E a))).1 (by
      rw [adicVal_map h]; exact (adicVal_le_one_iff K _).2 ⟨a, rfl⟩)
    exact ⟨b, hb⟩
  let e : K'.O ≃+* S := RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective K'.O K'.E (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩
  refine ⟨e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict S hS), fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict S hS a))
end GlobalTheory.UnitLemma.Unr.IntBasis
