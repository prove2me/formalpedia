-- Prove2me | solution 1 for GlobalTheory.LatComm.stab_commensurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:24.319668+00:00
-- url     : https://prove2.me/submissions/df64cfbb-af78-4773-b602-982506613067

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisFurther
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerCommensurableUnramifiedHermitia
import Theorems.Thm_GlobalTheory_LatComm_finite_between
import Theorems.Thm_GlobalTheory_LatComm_exists_pow_smul_le
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.LatComm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.LatComm
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Λ Λ' : Submodule L.O (Fin n → E)), IsLat L Λ → IsLat L Λ' → ∀ H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (H ⊓ stabL L Λ').relIndex (H ⊓ stabL L Λ) ≠ 0 ∧ ∀ g : ((Fin n → E) ≃ₗ[E] (Fin n → E)), IsLat L (g • Λ) ∧ stabL L (g • Λ) = MulAut.conj g • stabL L Λ := by
  intro F _ _ _ _ _ E _ _ _ L n Λ Λ' hΛ hΛ' H
  refine ⟨?_, fun g => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    obtain ⟨-, -, -, -, hO, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
    let p : L.O := ⟨algebraMap F E (ϖ : F), (hO _).2 ϖ.2⟩
    have hp : (p : E) = algebraMap F E (ϖ : F) := rfl
    obtain ⟨a, ha⟩ := exists_pow_smul_le L hϖ p hp hΛ hΛ'.1
    obtain ⟨b, hb⟩ := exists_pow_smul_le L hϖ p hp hΛ' hΛ.1
    have hfin : Finite (L.O ⧸ Ideal.span {p ^ (a + b)}) := by
      have h1 := hcard (a + b)
      have h2 : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ (a + b))} = {p ^ (a + b)} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff,
          SubmonoidClass.coe_pow, hp, map_pow]
      rw [h2] at h1
      apply Nat.finite_of_card_ne_zero
      rw [h1]
      exact pow_ne_zero _ (by omega)
    have hF := finite_between (p ^ (a + b)) Λ hΛ.1
    have hu : IsUnit ((p ^ a : L.O) : E) := by
      rw [SubmonoidClass.coe_pow, hp]
      exact ((IsUnit.mk0 _ (fun h => hϖ.ne_zero (Subtype.ext h))).map (algebraMap F E)).pow a
    have hinj : Function.Injective (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) := by
      intro x y h
      exact hu.smul_left_cancel.1 h
    have hcomm : ∀ (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (r : L.O) (v : Fin n → E),
        g • (r • v) = r • (g • v) := fun g r v => map_smul g (r : E) v
    have heq : (H ⊓ stabL L Λ').subgroupOf (H ⊓ stabL L Λ) =
        MulAction.stabilizer (H ⊓ stabL L Λ :) Λ' := by
      ext g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
    rw [Subgroup.relIndex, heq, MulAction.index_stabilizer]
    refine Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self Λ') ?_
    refine Set.Finite.of_finite_image
      (f := fun M => Submodule.map (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) M) (hF.subset ?_)
      (Submodule.map_injective_of_injective hinj).injOn
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have hg : g.1 • Λ = Λ := g.2.2
    refine ⟨?_, fun v hv => ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w g.1 Λ').1 hw
      show p ^ a • (g.1 • x) ∈ Λ
      rw [← hcomm]
      exact hg.le (Submodule.smul_mem_pointwise_smul _ _ _ (ha x hx))
    · rw [← hg] at hv
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v g.1 Λ).1 hv
      refine ⟨g.1 • (p ^ b • x), Submodule.smul_mem_pointwise_smul _ g.1 _ (hb x hx), ?_⟩
      rw [LinearMap.lsmul_apply, hcomm, pow_add, mul_smul]
  · exact hΛ.1.map _
  · rw [eq_top_iff]
    intro v _
    have hv : g.symm v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : (Fin n → E) →ₗ[E] (Fin n → E)) hv
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem_pointwise_smul _ g _ hx
  · exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g Λ
end GlobalTheory.LatComm
