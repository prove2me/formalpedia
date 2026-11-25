-- Prove2me | solution 1 for GlobalTheory.MoveFibre.fibre_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:28:37.847203+00:00
-- url     : https://prove2.me/submissions/ff56afec-a832-4803-8e1d-7011200d6681

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMoveScalarFibreMeasureOne
import Theorems.Thm_GlobalTheory_MoveFibre_cint_coset
import Theorems.Thm_GlobalTheory_MoveFibre_cj_hf_self
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFibre
namespace GlobalTheory.MoveFibre
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 0 ≤ S.a → ∀ u : S.V, (S.InZ u → cint S.refT (ind fun t : E => (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) = 1) ∧ ((∃ t : E, (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) → S.InZ u) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ u
  obtain ⟨htr, hO, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  have hfix : L.cj (S.h u u) = S.h u u := cj_hf_self L S.herm.1 u
  have h2 : algebraMap F E 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hT : ∀ t, t ∈ S.refT ↔ t + L.cj t = 0 ∧
      ∃ c ∈ L.O, algebraMap F E ((S.ϖ : F) ^ S.a) * c = t := fun t => Iff.rfl
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨x, hx, hxc⟩ := htr c
    rw [map_mul, ← hxc] at hc
    refine cint_coset _ _
      (algebraMap F E ((S.ϖ : F) ^ S.a) * x - algebraMap F E 2⁻¹ * S.h u u) fun t => ?_
    rw [hT]
    simp only [map_sub L.cj, map_mul L.cj, AlgEquiv.commutes, hfix]
    constructor
    · rintro ⟨⟨y, hy, e⟩, ht⟩
      exact ⟨by linear_combination ht + hc + S.h u u * h2,
        y - x, L.O.sub_mem hy hx, by linear_combination -e⟩
    · rintro ⟨ht, y, hy, e⟩
      exact ⟨⟨y + x, L.O.add_mem hy hx, by linear_combination -e⟩,
        by linear_combination ht - hc - S.h u u * h2⟩
  · rintro ⟨t, ⟨y, hy, e⟩, ht⟩
    obtain ⟨c, hc⟩ := (hO y hy).2.1
    refine ⟨c, ?_⟩
    have e' := congrArg L.cj e
    simp only [map_add L.cj, map_mul L.cj, AlgEquiv.commutes, hfix] at e'
    rw [map_mul, ← hc]
    linear_combination e + e' - ht - S.h u u * h2
end GlobalTheory.MoveFibre
