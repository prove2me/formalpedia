-- Prove2me | solution 1 for GlobalTheory.isFreeAction_specAction_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:31.824808+00:00
-- url     : https://prove2.me/submissions/0081fa9f-4f10-4a5f-a8f9-703982450f98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_FreeQuotient_isFreeRingAction_iff_inertia_eq_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (A : Type u) [CommRing A] [MulSemiringAction G A] :
    IsFreeAction (specAction G A) ↔ IsFreeRingAction G A := by
  constructor
  · intro h
    refine (FreeQuotient.isFreeRingAction_iff_inertia_eq_bot G A).mpr fun P hP ↦ ?_
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    let := Ideal.Quotient.field P
    refine inv_eq_one.mp (h (A ⧸ P) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))) g⁻¹ ?_)
    rw [specAction_hom, ← Spec.map_comp, inv_inv]
    congr 1
    ext a
    exact Ideal.Quotient.eq.mpr (AddSubgroup.mem_inertia.mp hg a)
  · intro h k _ x g hx
    obtain ⟨φ, rfl⟩ := Spec.map_surjective x
    rw [specAction_hom, ← Spec.map_comp, Spec.map_inj] at hx
    by_contra hg
    have := h g⁻¹ (by simpa using hg)
    refine RingHom.ker_ne_top φ.hom (top_le_iff.mp ?_)
    rw [← this, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact (RingHom.sub_mem_ker_iff _).mpr congr($hx a)
end GlobalTheory
